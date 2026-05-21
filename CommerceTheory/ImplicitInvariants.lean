import CommerceTheory.Logistics
import CommerceTheory.OpportunityPortfolio

namespace CommerceTheory

/-! ## Cross-module implicit invariants made explicit -/

/-!
Several domain records intentionally stay lightweight so individual modules can
be composed freely. This module adds reusable wrappers for assumptions that
cross those module boundaries: coupon caps, payment/order matching, event-stream
cursors, catalog publishability, experiment weights, and distributor sourcing.
-/

/-! ### Pricing and payment joins -/

/-- A coupon application that is both eligible and bounded by the subtotal. -/
structure BoundedCouponApplication where
  coupon : Coupon
  subtotal : Money
  usesBefore : Nat
  applicable : couponCanBeApplied coupon subtotal usesBefore
  amount_le_subtotal : coupon.amount ≤ subtotal

/-- Bounded coupon applications still satisfy the configured subtotal floor. -/
theorem boundedCoupon_application_meets_min_subtotal
    (application : BoundedCouponApplication) :
    application.coupon.minSubtotal ≤ application.subtotal := by
  exact application.applicable.left

/-- Bounded coupon applications still satisfy the configured usage cap. -/
theorem boundedCoupon_application_usage_below_max
    (application : BoundedCouponApplication) :
    application.usesBefore < application.coupon.maxUses := by
  exact application.applicable.right

/-- The discount amount of a bounded coupon fits inside the subtotal it is applied to. -/
theorem boundedCoupon_amount_le_subtotal
    (application : BoundedCouponApplication) :
    application.coupon.amount ≤ application.subtotal := by
  exact application.amount_le_subtotal

/-- Applying a bounded coupon conserves the original subtotal. -/
theorem boundedCoupon_subtotalAfter_add_amount_eq_subtotal
    (application : BoundedCouponApplication) :
    subtotalAfterCouponAmount application.subtotal application.coupon.amount +
      application.coupon.amount = application.subtotal := by
  unfold subtotalAfterCouponAmount
  exact Nat.sub_add_cancel application.amount_le_subtotal

/-- A captured payment paired with the exact order id, amount, and currency it settles. -/
structure CapturedPaymentMatchesOrder where
  order : Order
  payment : CapturedPayment
  order_matches : payment.orderId = order.id
  amount_matches : payment.amount = order.total
  currency_matches : payment.currency = order.currency

/-- Matched captured payments point at their validated order. -/
theorem capturedPaymentMatchesOrder_order_id
    (matchEvidence : CapturedPaymentMatchesOrder) :
    matchEvidence.payment.orderId = matchEvidence.order.id := by
  exact matchEvidence.order_matches

/-- Matched captured payments carry exactly the order total. -/
theorem capturedPaymentMatchesOrder_amount
    (matchEvidence : CapturedPaymentMatchesOrder) :
    matchEvidence.payment.amount = matchEvidence.order.total := by
  exact matchEvidence.amount_matches

/-- Matched captured payments use the order currency. -/
theorem capturedPaymentMatchesOrder_currency
    (matchEvidence : CapturedPaymentMatchesOrder) :
    matchEvidence.payment.currency = matchEvidence.order.currency := by
  exact matchEvidence.currency_matches

/-! ### Event-stream cursor validation -/

/-- Fold the last event sequence out of an event list, starting from a default cursor. -/
def eventStreamLastSequenceFrom : Nat → List EventEnvelope → Nat
  | last, [] => last
  | _, event :: rest => eventStreamLastSequenceFrom event.sequence rest

/-- The cursor implied by replaying an event stream from sequence zero. -/
def eventStreamComputedLastSequence (stream : EventStream) : Nat :=
  eventStreamLastSequenceFrom 0 stream.events

/-- An event stream whose ordering and stored cursor have both been validated. -/
structure ValidEventStream where
  stream : EventStream
  sequences_strict : streamSequencesStrictlyIncrease stream
  lastSequence_correct : stream.lastSequence = eventStreamComputedLastSequence stream

/-- Valid event streams expose strict sequence ordering. -/
theorem validEventStream_sequences_strict (stream : ValidEventStream) :
    streamSequencesStrictlyIncrease stream.stream := by
  exact stream.sequences_strict

/-- Valid event streams expose that the stored cursor is the computed last sequence. -/
theorem validEventStream_lastSequence_correct (stream : ValidEventStream) :
    stream.stream.lastSequence = eventStreamComputedLastSequence stream.stream := by
  exact stream.lastSequence_correct

/-- The first event in a nonempty valid stream must be newer than sequence zero. -/
theorem validEventStream_first_sequence_positive
    (stream : ValidEventStream) (event : EventEnvelope) (rest : List EventEnvelope)
    (hEvents : stream.stream.events = event :: rest) :
    0 < event.sequence := by
  have hStrict : streamSequencesStrictlyIncreaseFrom 0 (event :: rest) := by
    have hOrdered := stream.sequences_strict
    unfold streamSequencesStrictlyIncrease at hOrdered
    rw [← hEvents]
    exact hOrdered
  exact streamSequencesStrictlyIncreaseFrom_head 0 event rest hStrict

/-! ### Catalog, marketplace, and feed publishability -/

/-- Active catalog products are the only products eligible for sale. -/
def productActive (product : Product) : Prop :=
  product.status = ProductStatus.Active

/-- Active variants are the only variants eligible for sale. -/
def variantActive (variant : ProductVariant) : Prop :=
  variant.active = true

/-- A catalog entry whose product and variant are both sellable. -/
structure SellableCatalogEntry where
  entry : ProductCatalogEntry
  product_active : productActive entry.product
  variant_active : variantActive entry.variant

/-- Sellable catalog entries still preserve product/variant identity. -/
theorem sellableCatalogEntry_variant_belongs_to_product
    (entry : SellableCatalogEntry) :
    entry.entry.variant.productId = entry.entry.product.id := by
  exact entry.entry.variant_belongs_to_product

/-- Sellable catalog entries expose that the product is active. -/
theorem sellableCatalogEntry_product_active (entry : SellableCatalogEntry) :
    entry.entry.product.status = ProductStatus.Active := by
  exact entry.product_active

/-- Sellable catalog entries expose that the variant is active. -/
theorem sellableCatalogEntry_variant_active (entry : SellableCatalogEntry) :
    entry.entry.variant.active = true := by
  exact entry.variant_active

/-- Feed lines with positive published stock. -/
def feedLineHasStock (line : SafeProductFeedLine) : Prop :=
  0 < line.stock

/-- A feed line that is safe and publishable because it has stock. -/
structure PublishableFeedLine where
  line : SafeProductFeedLine
  has_stock : feedLineHasStock line

/-- Publishable feed lines preserve SKU identity with the stock source. -/
theorem publishableFeedLine_same_sku (line : PublishableFeedLine) :
    line.line.sku = line.line.stockState.sku := by
  exact line.line.same_sku

/-- Publishable feed lines keep price inside the channel policy. -/
theorem publishableFeedLine_price_valid (line : PublishableFeedLine) :
    line.line.pricePolicy.minPrice ≤ line.line.price ∧
      line.line.price ≤ line.line.pricePolicy.maxPrice := by
  exact line.line.price_valid

/-- Publishable feed lines expose their positive stock guarantee. -/
theorem publishableFeedLine_stock_positive (line : PublishableFeedLine) :
    0 < line.line.stock := by
  exact line.has_stock

/-- Publishable feed lines imply the source stock has positive available quantity. -/
theorem publishableFeedLine_available_positive (line : PublishableFeedLine) :
    0 < availableStock line.line.stockState := by
  exact lt_of_lt_of_le line.has_stock line.line.stock_safe

/-! ### Experiment and distributor sourcing guards -/

/-- Any variant in a traffic list has weight no larger than the list total. -/
theorem experimentVariant_trafficWeight_le_total
    (variant : ExperimentVariant) (variants : List ExperimentVariant)
    (hmem : variant ∈ variants) :
    variant.trafficWeight ≤ experimentTrafficTotal variants := by
  induction variants with
  | nil =>
      cases hmem
  | cons head rest ih =>
      simp [experimentTrafficTotal] at hmem ⊢
      rcases hmem with h | h
      · rw [h]
        exact Nat.le_add_right head.trafficWeight (experimentTrafficTotal rest)
      · exact (ih h).trans
          (Nat.le_add_left (experimentTrafficTotal rest) head.trafficWeight)

/-- Every variant in a validated experiment has traffic weight at most 100. -/
theorem experimentVariant_trafficWeight_le_100
    (experiment : Experiment) (variant : ExperimentVariant)
    (hmem : variant ∈ experiment.variants) :
    variant.trafficWeight ≤ 100 := by
  rw [← experiment.traffic_total_100]
  exact experimentVariant_trafficWeight_le_total variant experiment.variants hmem

/-- Active distributor products are eligible for sourcing. -/
def distributorProductActive (product : DistributorProduct) : Prop :=
  product.active = true

/-- A distributor product can source a quantity when it is active and within its bounds. -/
def distributorProductCanSource (product : DistributorProduct) (units : Quantity) : Prop :=
  distributorProductActive product ∧ product.minOrderQty ≤ units ∧ units ≤ product.availableQty

/-- A distributor product paired with a sourceable quantity. -/
structure SourceableDistributorProduct where
  product : DistributorProduct
  units : Quantity
  can_source : distributorProductCanSource product units

/-- Sourceable distributor products are active. -/
theorem sourceableDistributorProduct_active
    (source : SourceableDistributorProduct) :
    source.product.active = true := by
  exact source.can_source.left

/-- Sourceable quantities satisfy the distributor minimum order quantity. -/
theorem sourceableDistributorProduct_min_order
    (source : SourceableDistributorProduct) :
    source.product.minOrderQty ≤ source.units := by
  exact source.can_source.right.left

/-- Sourceable quantities fit inside the distributor's available quantity. -/
theorem sourceableDistributorProduct_available
    (source : SourceableDistributorProduct) :
    source.units ≤ source.product.availableQty := by
  exact source.can_source.right.right

/-! ### Second-pass joins across the remaining modules -/

/-- A bounded coupon application that also passed the fraud policy's usage limit. -/
structure FraudCheckedCouponApplication where
  application : BoundedCouponApplication
  policy : FraudPolicy
  uses_allowed : couponUsesAllowed policy application.usesBefore

/-- Fraud-checked coupon use stays inside the fraud policy cap. -/
theorem fraudCheckedCoupon_uses_allowed
    (application : FraudCheckedCouponApplication) :
    application.application.usesBefore ≤ application.policy.maxCouponUses := by
  exact application.uses_allowed

/-- Fraud-checked coupon use still stays below the coupon's own max-use counter. -/
theorem fraudCheckedCoupon_below_coupon_max
    (application : FraudCheckedCouponApplication) :
    application.application.usesBefore < application.application.coupon.maxUses := by
  exact application.application.applicable.right

/-- A payment-capture journal tied to the captured payment amount it projects. -/
structure CapturedPaymentJournalProjection where
  accounts : AccountingAccounts
  payment : CapturedPayment
  journal : BalancedJournalEntry
  journal_correct : journal = paymentCapturedJournal accounts payment.amount

/-- Payment-capture projections are balanced. -/
theorem capturedPaymentJournalProjection_balanced
    (projection : CapturedPaymentJournalProjection) :
    debitTotal projection.journal.postings =
      creditTotal projection.journal.postings := by
  rw [projection.journal_correct]
  exact paymentCapturedJournal_balanced projection.accounts projection.payment.amount

/-- Payment-capture projections debit cash for the captured amount. -/
theorem capturedPaymentJournalProjection_debit_amount
    (projection : CapturedPaymentJournalProjection) :
    debitTotal projection.journal.postings = projection.payment.amount := by
  rw [projection.journal_correct]
  exact paymentCapturedJournal_debitTotal projection.accounts projection.payment.amount

/-- Payment-capture projections credit deferred revenue for the captured amount. -/
theorem capturedPaymentJournalProjection_credit_amount
    (projection : CapturedPaymentJournalProjection) :
    creditTotal projection.journal.postings = projection.payment.amount := by
  rw [projection.journal_correct]
  exact paymentCapturedJournal_creditTotal projection.accounts projection.payment.amount

/-- A refund journal tied to a refundable ledger amount. -/
structure RefundJournalProjection where
  accounts : AccountingAccounts
  ledger : PaymentLedger
  amount : Money
  refundable : canRefund ledger amount
  journal : BalancedJournalEntry
  journal_correct : journal = refundIssuedJournal accounts amount

/-- Refund journal projections are balanced. -/
theorem refundJournalProjection_balanced
    (projection : RefundJournalProjection) :
    debitTotal projection.journal.postings =
      creditTotal projection.journal.postings := by
  rw [projection.journal_correct]
  exact refundIssuedJournal_balanced projection.accounts projection.amount

/-- Refund journal projections debit refunds for exactly the refundable amount. -/
theorem refundJournalProjection_debit_amount
    (projection : RefundJournalProjection) :
    debitTotal projection.journal.postings = projection.amount := by
  rw [projection.journal_correct]
  exact refundIssuedJournal_debitTotal projection.accounts projection.amount

/-- Refund journal projections credit cash for exactly the refundable amount. -/
theorem refundJournalProjection_credit_amount
    (projection : RefundJournalProjection) :
    creditTotal projection.journal.postings = projection.amount := by
  rw [projection.journal_correct]
  exact refundIssuedJournal_creditTotal projection.accounts projection.amount

/-- Refund journal projections cannot exceed the remaining refundable balance. -/
theorem refundJournalProjection_amount_le_remaining
    (projection : RefundJournalProjection) :
    projection.amount ≤ remainingRefundAmount projection.ledger := by
  exact canRefund_amount_le_remaining
    projection.ledger projection.amount projection.refundable

/-- A synced marketplace listing that is also active and in stock for advertising. -/
structure AdvertisableSyncedMarketplaceListing where
  synced : SyncedMarketplaceListing
  can_advertise : listingCanBeAdvertised synced.listing

/-- Advertisable synced listings are active. -/
theorem advertisableSyncedListing_active
    (listing : AdvertisableSyncedMarketplaceListing) :
    listing.synced.listing.status = ListingStatus.Active := by
  exact listing.can_advertise.left

/-- Advertisable synced listings publish positive stock. -/
theorem advertisableSyncedListing_in_stock
    (listing : AdvertisableSyncedMarketplaceListing) :
    0 < listing.synced.listing.publishedStock := by
  exact listing.can_advertise.right

/-- Advertisable synced listings imply positive internal available stock. -/
theorem advertisableSyncedListing_available_positive
    (listing : AdvertisableSyncedMarketplaceListing) :
    0 < availableStock listing.synced.stock := by
  exact lt_of_lt_of_le listing.can_advertise.right
    listing.synced.publishedStock_le_available

/-- A wholesale checkout authorized by customer eligibility, terms, and credit limit. -/
structure WholesaleCreditCheckout where
  account : WholesaleCreditAccount
  lines : List WholesaleLine
  terms : PaymentTerms
  orderTotal : Money
  total_correct : orderTotal = wholesaleOrderNetTotal lines
  terms_allowed : paymentTermsAllowed TradeMode.Wholesale terms
  credit_ok : canPlaceWholesaleCreditOrder account orderTotal

/-- Wholesale credit checkouts belong to approved wholesale customers. -/
theorem wholesaleCreditCheckout_customer_can_buy
    (checkout : WholesaleCreditCheckout) :
    customerCanBuyWholesale checkout.account.customer := by
  exact checkout.account.customer_can_buy_wholesale

/-- Wholesale credit checkouts keep outstanding credit inside the configured limit. -/
theorem wholesaleCreditCheckout_credit_safe
    (checkout : WholesaleCreditCheckout) :
    checkout.account.outstanding + checkout.orderTotal ≤ checkout.account.creditLimit := by
  exact checkout.credit_ok

/-- Wholesale credit checkouts keep the computed net total inside the credit limit. -/
theorem wholesaleCreditCheckout_computed_total_credit_safe
    (checkout : WholesaleCreditCheckout) :
    checkout.account.outstanding + wholesaleOrderNetTotal checkout.lines ≤
      checkout.account.creditLimit := by
  rw [← checkout.total_correct]
  exact checkout.credit_ok

/-- Wholesale checkout net totals remain bounded by their retail-equivalent totals. -/
theorem wholesaleCreditCheckout_net_le_retail_equivalent
    (checkout : WholesaleCreditCheckout) :
    wholesaleOrderNetTotal checkout.lines ≤ wholesaleRetailEquivalentTotal checkout.lines := by
  exact wholesaleOrderNetTotal_le_retailEquivalentTotal checkout.lines

/-- A competitor benchmark whose best offer is fresh enough and trusted for automation. -/
structure TrustedFreshCompetitorBenchmark where
  benchmark : CompetitorPriceBenchmark
  now : Timestamp
  maxAge : Timestamp
  trust : TrustLevel
  fresh_best_offer : priceSnapshotFresh now maxAge benchmark.bestOffer.observedAt
  trust_allows_auto : trustAllowsAutoRepricing trust

/-- Trusted fresh benchmarks expose that the best offer was not observed in the future. -/
theorem trustedFreshBenchmark_observedAt_le_now
    (benchmark : TrustedFreshCompetitorBenchmark) :
    benchmark.benchmark.bestOffer.observedAt ≤ benchmark.now := by
  exact benchmark.fresh_best_offer.left

/-- Trusted fresh benchmarks expose that the best offer is within the accepted age. -/
theorem trustedFreshBenchmark_age_le_maxAge
    (benchmark : TrustedFreshCompetitorBenchmark) :
    benchmark.now - benchmark.benchmark.bestOffer.observedAt ≤ benchmark.maxAge := by
  exact benchmark.fresh_best_offer.right

/-- Trusted fresh benchmarks keep the usual relevance proof for the best offer. -/
theorem trustedFreshBenchmark_best_offer_relevant
    (benchmark : TrustedFreshCompetitorBenchmark) :
    competitorOfferRelevant
      benchmark.benchmark.bestOffer benchmark.benchmark.sku benchmark.benchmark.currency := by
  exact benchmark.benchmark.bestOffer_relevant

/-- A competitor-aware offer whose advertised price also respects the brand MAP policy. -/
structure MapCompliantCompetitorAwareOffer where
  offer : CompetitorAwareDropshipOffer
  policy : BrandPricingPolicy
  advertised_ok : advertisedPriceAllowed policy offer.offer.saleUnitPrice

/-- MAP-compliant competitor-aware offers keep the advertised price at or above MAP. -/
theorem mapCompliantCompetitorAwareOffer_map_safe
    (offer : MapCompliantCompetitorAwareOffer) :
    offer.policy.mapPrice ≤ offer.offer.offer.saleUnitPrice := by
  exact offer.advertised_ok

/-- MAP-compliant competitor-aware offers retain the existing profit guarantee. -/
theorem mapCompliantCompetitorAwareOffer_profit_safe
    (offer : MapCompliantCompetitorAwareOffer) :
    offer.offer.minProfit ≤
      profitAtOfferPrice offer.offer.offer.saleUnitPrice offer.offer.discount offer.offer.costs := by
  exact competitorAwareDropshipOffer_profit_guaranteed offer.offer

/-- Runtime-currency conversion evidence for amounts converted through a fresh FX rate. -/
structure FreshCurrencyConversion where
  sourceAmount : MoneyAmount
  rate : ExchangeRate
  targetAmount : MoneyAmount
  now : Timestamp
  maxAge : Timestamp
  source_matches_rate : sourceAmount.currency = rate.source
  target_matches_rate : targetAmount.currency = rate.target
  amount_correct : targetAmount.amount = convertMoneyFloor sourceAmount.amount rate
  rate_fresh : fxQuoteFresh now maxAge rate

/-- Fresh currency conversions expose their source currency check. -/
theorem freshCurrencyConversion_source_matches
    (conversion : FreshCurrencyConversion) :
    conversion.sourceAmount.currency = conversion.rate.source := by
  exact conversion.source_matches_rate

/-- Fresh currency conversions expose their target currency check. -/
theorem freshCurrencyConversion_target_matches
    (conversion : FreshCurrencyConversion) :
    conversion.targetAmount.currency = conversion.rate.target := by
  exact conversion.target_matches_rate

/-- Fresh currency conversions compute the target amount from the rate. -/
theorem freshCurrencyConversion_amount_correct
    (conversion : FreshCurrencyConversion) :
    conversion.targetAmount.amount =
      convertMoneyFloor conversion.sourceAmount.amount conversion.rate := by
  exact conversion.amount_correct

/-- Fresh currency conversions use a rate that was not observed in the future. -/
theorem freshCurrencyConversion_rate_observedAt_le_now
    (conversion : FreshCurrencyConversion) :
    conversion.rate.observedAt ≤ conversion.now := by
  exact conversion.rate_fresh.left

/-- Fresh currency conversions use a rate within the accepted age window. -/
theorem freshCurrencyConversion_rate_age_le_maxAge
    (conversion : FreshCurrencyConversion) :
    conversion.now - conversion.rate.observedAt ≤ conversion.maxAge := by
  exact conversion.rate_fresh.right

/-- A gift-card redemption paired with the timestamp at which the card was valid. -/
structure ValidGiftCardRedemptionAt where
  now : Timestamp
  redemption : GiftCardRedemption
  not_expired : giftCardValidAt now redemption.card

/-- Time-valid gift-card redemptions have not passed expiry. -/
theorem validGiftCardRedemptionAt_not_expired
    (redemption : ValidGiftCardRedemptionAt) :
    redemption.now ≤ redemption.redemption.card.expiresAt := by
  exact redemption.not_expired

/-- Time-valid gift-card redemptions still conserve card balance. -/
theorem validGiftCardRedemptionAt_balance_conservation
    (redemption : ValidGiftCardRedemptionAt) :
    giftCardBalanceAfterRedeem redemption.redemption + redemption.redemption.amount =
      redemption.redemption.card.balance := by
  exact giftCardBalanceAfterRedeem_add_amount_eq_balance redemption.redemption

/-- A chargeback linked to the captured payment amount it disputes. -/
structure ChargebackForCapturedPayment where
  payment : CapturedPayment
  chargeback : Chargeback
  payment_amount_matches : chargeback.paymentAmount = payment.amount

/-- Chargebacks linked to captured payments cannot exceed the captured amount. -/
theorem chargebackForCapturedPayment_amount_safe
    (chargeback : ChargebackForCapturedPayment) :
    chargeback.chargeback.chargebackAmount ≤ chargeback.payment.amount := by
  rw [← chargeback.payment_amount_matches]
  exact chargeback.chargeback.amount_le_payment

/-- Forecasts suitable for automatic replenishment. -/
def demandForecastActionable (forecast : DemandForecast) : Prop :=
  confidenceAllowsAutoReplenish forecast.confidence ∧
    0 < forecast.expectedUnits ∧ 0 < forecast.horizonDays

/-- A demand forecast with all gates needed for automatic replenishment. -/
structure ActionableDemandForecast where
  forecast : DemandForecast
  actionable : demandForecastActionable forecast

/-- Actionable forecasts have enough confidence for automatic replenishment. -/
theorem actionableDemandForecast_confidence_allows
    (forecast : ActionableDemandForecast) :
    confidenceAllowsAutoReplenish forecast.forecast.confidence := by
  exact forecast.actionable.left

/-- Actionable forecasts predict positive demand. -/
theorem actionableDemandForecast_expectedUnits_positive
    (forecast : ActionableDemandForecast) :
    0 < forecast.forecast.expectedUnits := by
  exact forecast.actionable.right.left

/-- Actionable forecasts use a positive planning horizon. -/
theorem actionableDemandForecast_horizon_positive
    (forecast : ActionableDemandForecast) :
    0 < forecast.forecast.horizonDays := by
  exact forecast.actionable.right.right

/-- Supplier quality that is both policy-approved and orderable right now. -/
structure ApprovedOrderableSupplierQuality where
  quality : ApprovedSupplierQuality
  can_receive_orders : supplierCanReceiveOrders quality.supplier

/-- Approved orderable suppliers satisfy all quality thresholds. -/
theorem approvedOrderableSupplierQuality_quality_ok
    (supplier : ApprovedOrderableSupplierQuality) :
    supplier.quality.metrics.defectRateBps ≤ supplier.quality.policy.maxDefectRateBps ∧
      supplier.quality.metrics.lateShipmentRateBps ≤
        supplier.quality.policy.maxLateShipmentRateBps ∧
      supplier.quality.metrics.cancellationRateBps ≤
        supplier.quality.policy.maxCancellationRateBps := by
  exact approvedSupplier_quality_ok supplier.quality

/-- Approved orderable suppliers are active. -/
theorem approvedOrderableSupplierQuality_active
    (supplier : ApprovedOrderableSupplierQuality) :
    supplier.quality.supplier.active = true := by
  exact supplier.can_receive_orders.left

/-- Approved orderable suppliers are not suspended. -/
theorem approvedOrderableSupplierQuality_not_suspended
    (supplier : ApprovedOrderableSupplierQuality) :
    supplier.quality.supplier.suspended = false := by
  exact supplier.can_receive_orders.right

/-! ### CRM and logistics joins -/

/-- A converted lead paired with the opportunity created from it. -/
structure ConvertedLeadOpportunity where
  lead : Lead
  opportunity : SalesOpportunity
  lead_converted : lead.status = LeadStatus.Converted
  opportunity_source_matches : opportunity.sourceLead = some lead.id
  account_matches : opportunity.accountId = lead.accountId
  contact_matches : opportunity.contactId = lead.contactId
  currency_matches : opportunity.currency = lead.currency
  opportunity_amount_le_estimate : opportunity.amount ≤ lead.estimatedValue

/-- Converted lead opportunities expose the terminal converted lead status. -/
theorem convertedLeadOpportunity_status
    (conversion : ConvertedLeadOpportunity) :
    conversion.lead.status = LeadStatus.Converted := by
  exact conversion.lead_converted

/-- Converted lead opportunities keep the opportunity source pointer. -/
theorem convertedLeadOpportunity_source_matches
    (conversion : ConvertedLeadOpportunity) :
    conversion.opportunity.sourceLead = some conversion.lead.id := by
  exact conversion.opportunity_source_matches

/-- Converted opportunity amounts remain inside the lead estimate. -/
theorem convertedLeadOpportunity_amount_le_estimate
    (conversion : ConvertedLeadOpportunity) :
    conversion.opportunity.amount ≤ conversion.lead.estimatedValue := by
  exact conversion.opportunity_amount_le_estimate

/-- A customer order associated with a CRM account and contact. -/
structure CRMOrderContact where
  account : CRMAccount
  contact : CRMContact
  order : Order
  account_active : crmAccountActive account
  contact_account_matches : contact.accountId = account.id
  contact_customer_matches : contact.customerId = account.customer.id

/-- CRM order contacts require an active CRM account. -/
theorem crmOrderContact_account_active (x : CRMOrderContact) :
    x.account.status = CRMAccountStatus.Active := by
  exact x.account_active

/-- CRM order contacts link the contact to the owning account. -/
theorem crmOrderContact_account_matches (x : CRMOrderContact) :
    x.contact.accountId = x.account.id := by
  exact x.contact_account_matches

/-- CRM order contacts link the contact to the account's commerce customer. -/
theorem crmOrderContact_customer_matches (x : CRMOrderContact) :
    x.contact.customerId = x.account.customer.id := by
  exact x.contact_customer_matches

/-- A logistics shipment plan tied to a CRM-associated customer order. -/
structure ShipmentForCRMOrder where
  crmOrder : CRMOrderContact
  plan : LogisticsShipmentPlan
  order_matches : plan.order = crmOrder.order

/-- Shipments for CRM orders point at the same order id. -/
theorem shipmentForCRMOrder_order_id_matches
    (shipment : ShipmentForCRMOrder) :
    shipment.plan.order.id = shipment.crmOrder.order.id := by
  rw [shipment.order_matches]

/-- Shipments for CRM orders inherit the carrier weight safety check. -/
theorem shipmentForCRMOrder_package_weight_safe
    (shipment : ShipmentForCRMOrder) :
    shipment.plan.package.weight ≤ shipment.plan.quote.service.maxWeight := by
  exact shipmentPlan_package_weight_safe shipment.plan

/-- A logistics exception escalated into a CRM support case. -/
structure LogisticsExceptionSupportCase where
  exception : LogisticsException
  shipment : LogisticsShipmentPlan
  supportCase : SupportCase
  exception_shipment_matches : exception.shipmentId = shipment.id
  support_case_order_matches : supportCase.orderId = some shipment.order.id
  support_case_escalated : supportCase.status = SupportCaseStatus.Escalated
  exception_raised_before_case_opened : exception.raisedAt ≤ supportCase.openedAt

/-- Escalated logistics exceptions point at the affected shipment. -/
theorem logisticsExceptionSupportCase_shipment_matches
    (escalation : LogisticsExceptionSupportCase) :
    escalation.exception.shipmentId = escalation.shipment.id := by
  exact escalation.exception_shipment_matches

/-- Escalated logistics support cases point at the affected order. -/
theorem logisticsExceptionSupportCase_order_matches
    (escalation : LogisticsExceptionSupportCase) :
    escalation.supportCase.orderId = some escalation.shipment.order.id := by
  exact escalation.support_case_order_matches

/-- Escalated logistics exceptions use an escalated CRM support case. -/
theorem logisticsExceptionSupportCase_status_escalated
    (escalation : LogisticsExceptionSupportCase) :
    escalation.supportCase.status = SupportCaseStatus.Escalated := by
  exact escalation.support_case_escalated

/-- Escalated support cases are not opened before the logistics exception exists. -/
theorem logisticsExceptionSupportCase_opened_after_exception
    (escalation : LogisticsExceptionSupportCase) :
    escalation.exception.raisedAt ≤ escalation.supportCase.openedAt := by
  exact escalation.exception_raised_before_case_opened

/-- A CRM-approved return authorization tied to physical logistics return handling. -/
structure CRMApprovedReturnHandling where
  authorization : ReturnAuthorization
  receipt : ReturnReceipt
  approved : returnAuthorizationApproved authorization
  receipt_matches_authorization : receipt.authorization = authorization

/-- CRM-approved return handling exposes the approved authorization state. -/
theorem crmApprovedReturnHandling_approved
    (handling : CRMApprovedReturnHandling) :
    handling.authorization.status = ReturnAuthorizationStatus.Approved := by
  exact handling.approved

/-- CRM-approved return handling cannot refund above the ledger's remaining amount. -/
theorem crmApprovedReturnHandling_refund_le_remaining
    (handling : CRMApprovedReturnHandling) :
    handling.receipt.refundIssued ≤ remainingRefundAmount handling.authorization.ledger := by
  have hReceipt : handling.receipt.refundIssued ≤ handling.authorization.refundAmount := by
    have h := handling.receipt.refund_le_authorized
    rw [handling.receipt_matches_authorization] at h
    exact h
  exact hReceipt.trans (returnAuthorization_refund_le_remaining handling.authorization)

/-- CRM-approved return handling cannot refund above the original order total. -/
theorem crmApprovedReturnHandling_refund_le_order_total
    (handling : CRMApprovedReturnHandling) :
    handling.receipt.refundIssued ≤ handling.authorization.order.total := by
  have h := returnReceipt_refund_le_order_total handling.receipt
  rw [handling.receipt_matches_authorization] at h
  exact h

/-- CRM-approved return handling cannot receive more units than the original order held. -/
theorem crmApprovedReturnHandling_received_le_order_quantity
    (handling : CRMApprovedReturnHandling) :
    handling.receipt.receivedQuantity ≤ cartQuantityTotal handling.authorization.order.items := by
  have hReceipt : handling.receipt.receivedQuantity ≤ handling.authorization.quantity := by
    have h := handling.receipt.received_le_authorized
    rw [handling.receipt_matches_authorization] at h
    exact h
  exact hReceipt.trans handling.authorization.quantity_le_order_quantity

end CommerceTheory
