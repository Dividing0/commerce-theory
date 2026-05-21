import CommerceTheory.EventLanguage
import CommerceTheory.EventReplay
import CommerceTheory.ImplicitInvariants
import CommerceTheory.InventoryAlgorithms
import CommerceTheory.KeyedTotals
import CommerceTheory.OpportunityRanking
import CommerceTheory.Tax
import CommerceTheory.Validation
import CommerceTheory.Workflow

namespace CommerceTheory

/-! ## 19. Main summary theorems -/

/-!
The summary module re-exports the headline guarantees proved across the domain:
validated orders are price-safe, dropship fulfillment is cost-safe, and
competitor-aware offers preserve their stated minimum profit.
-/

/-- Core pricing safety for any validated customer order. -/
theorem production_order_pricing_safety (order : Order) :
    order.total ≤ cartGrossTotal order.items + order.shippingMethod.price + order.tax := by
  exact order_total_is_safe order

/-- Core dropshipping cost safety for any validated dropship fulfillment. -/
theorem dropship_core_cost_safety (fulfillment : DropshipFulfillment) :
    dropshipSupplierCostTotal fulfillment.purchaseOrder.lines ≤ fulfillment.customerOrder.total := by
  exact dropshipFulfillment_supplierCost_le_orderTotal fulfillment

/-- Any competitor-aware dropship offer is profit-safe under its stated model. -/
theorem competitor_aware_dropship_offer_is_profit_safe
    (x : CompetitorAwareDropshipOffer) :
    x.minProfit ≤ profitAtOfferPrice x.offer.saleUnitPrice x.discount x.costs := by
  exact competitorAwareDropshipOffer_profit_guaranteed x

/-- Signed profit/loss preserves loss cases instead of flooring them to zero. -/
theorem signed_profit_loss_records_loss
    (revenue totalCosts : Money) (h : revenue < totalCosts) :
    profitLossAmount revenue totalCosts < 0 := by
  exact profitLossAmount_negative_if_revenue_lt_costs revenue totalCosts h

/-- Guaranteed dropship quotes carry a signed profit/loss proof as well as non-negative profit. -/
theorem guaranteed_quote_signed_profit_safety
    (quote : GuaranteedDropshipProfitQuote) :
    Int.ofNat quote.minProfit ≤ quote.signedProfit := by
  exact guaranteedQuote_signedProfit_ge_minProfit quote

/-- Cart totals conserve gross value: net revenue plus discounts equals gross. -/
theorem cart_discount_conservation (items : List CartLine) :
    cartNetTotal items + cartDiscountTotal items = cartGrossTotal items := by
  exact cartNetTotal_plus_discountTotal_eq_grossTotal items

/-- Issuing a validated refund preserves the payment-ledger cap. -/
theorem refund_ledger_safety
    (ledger : PaymentLedger) (amount : Money) (h : canRefund ledger amount) :
    (issueRefund ledger amount h).refunded ≤ (issueRefund ledger amount h).captured := by
  exact issueRefund_preserves_safety ledger amount h

/-- Payment-capture journal projections remain double-entry balanced. -/
theorem payment_capture_accounting_safety
    (accounts : AccountingAccounts) (amount : Money) :
    debitTotal (paymentCapturedJournal accounts amount).postings =
      creditTotal (paymentCapturedJournal accounts amount).postings := by
  exact paymentCapturedJournal_balanced accounts amount

/-- Approved suppliers satisfy every modeled quality threshold. -/
theorem approved_supplier_quality_safety (a : ApprovedSupplierQuality) :
    a.metrics.defectRateBps ≤ a.policy.maxDefectRateBps ∧
      a.metrics.lateShipmentRateBps ≤ a.policy.maxLateShipmentRateBps ∧
      a.metrics.cancellationRateBps ≤ a.policy.maxCancellationRateBps := by
  exact approvedSupplier_quality_ok a

/-- Selected opportunity portfolios cover their aggregate minimum-profit floor. -/
theorem opportunity_portfolio_profit_floor_safety
    (p : DropshipOpportunityPortfolio) :
    candidatesMinProfitTotal p.selected ≤ candidatesProfitTotal p.selected := by
  exact opportunityPortfolio_expectedProfit_covers_minProfit p

/-- Fulfillment plans cannot request more than the available stock they allocate. -/
theorem fulfillment_plan_available_stock_safety (p : FulfillmentPlan) :
    p.requested ≤ allocationsAvailableTotal p.allocations := by
  exact fulfillmentPlan_requested_le_availableTotal p

/-! ### Inventory concurrency and fulfillment realism theorems -/

/-- Compare-and-swap reservations either fail or advance versioned stock safely. -/
theorem inventory_compare_and_swap_reservation_safety
    (stock : VersionedStock) (quantity expectedVersion : Nat)
    (next : VersionedStock)
    (hSuccess : compareAndSwapReserve? stock quantity expectedVersion = some next) :
    next.version = stock.version + 1 ∧ next.reserved ≤ next.total := by
  exact ⟨compareAndSwapReserve?_success_increases_version
      stock quantity expectedVersion next hSuccess,
    compareAndSwapReserve?_success_preserves_safety
      stock quantity expectedVersion next hSuccess⟩

/-- Stale expected versions are rejected before reservation state changes. -/
theorem inventory_compare_and_swap_stale_rejected
    (stock : VersionedStock) (quantity expectedVersion : Nat)
    (hStale : expectedVersion ≠ stock.version) :
    compareAndSwapReserve? stock quantity expectedVersion = none := by
  exact compareAndSwapReserve?_stale_fails stock quantity expectedVersion hStale

/-- Concurrent reservation conflicts make the second observed version stale after success. -/
theorem concurrent_reservation_conflict_safety
    (conflict : ConcurrentReservationConflict)
    (hFirstVersion : conflict.first.expectedVersion = conflict.first.stock.version)
    (hFirstQty : canReserve conflict.first.stock.toStockState conflict.first.quantity) :
    conflict.first.stock.sku = conflict.second.stock.sku ∧
      conflict.first.expectedVersion = conflict.second.expectedVersion ∧
      conflict.second.expectedVersion ≠
        (reserveVersionedStock
          conflict.first.stock
          conflict.first.quantity
          conflict.first.expectedVersion
          hFirstVersion
          hFirstQty).version := by
  exact ⟨concurrentReservationConflict_same_sku conflict,
    concurrentReservationConflict_same_expected_version conflict,
    concurrentReservationConflict_second_version_stale_after_first
      conflict hFirstVersion hFirstQty⟩

/-- Expired reservations cannot be active and can be released without breaking stock safety. -/
theorem expired_reservation_release_safety
    (reservation : TimedReservation) (now : Timestamp)
    (hExpired : reservationExpiredAt now reservation) :
    ¬ reservationActiveAt now reservation ∧
      (releaseExpiredReservation reservation now hExpired).reserved ≤
        (releaseExpiredReservation reservation now hExpired).total := by
  exact ⟨expiredReservation_not_activeAt reservation now hExpired,
    releaseExpiredReservation_preserves_safety reservation now hExpired⟩

/-- Confirming held stock ships it without decrementing available stock a second time. -/
theorem confirmed_reserved_shipment_inventory_safety
    (stock : StockState) (quantity : Quantity)
    (hReserved : quantity ≤ stock.reserved) :
    (confirmReservedShipment stock quantity hReserved).reserved ≤
        (confirmReservedShipment stock quantity hReserved).total ∧
      availableStock (confirmReservedShipment stock quantity hReserved) =
        availableStock stock := by
  exact ⟨confirmReservedShipment_preserves_safety stock quantity hReserved,
    confirmReservedShipment_available_eq stock quantity hReserved⟩

/-- Backorder and preorder records conserve request quantities and capacity. -/
theorem backorder_preorder_inventory_safety
    (backorder : BackorderRequest) (preorder : PreorderReservation) :
    backorder.availableNow + backorder.backordered = backorder.requested ∧
      backorder.backordered ≤ backorder.requested ∧
      preorder.quantity ≤ preorder.window.capacity ∧
      preorder.window.opensAt ≤ preorder.reservedAt ∧
      preorder.reservedAt ≤ preorder.window.closesAt := by
  exact ⟨backorderRequest_conserves_quantity backorder,
    backorderRequest_backordered_le_requested backorder,
    preorderReservation_quantity_le_capacity preorder,
    (preorderReservation_in_window preorder).left,
    (preorderReservation_in_window preorder).right⟩

/-- Serialized, lot, and substitution inventory proofs compose for sellable stock. -/
theorem serialized_lot_substitution_inventory_safety
    (serialized : SerializedInventorySet) (lot : InventoryLot)
    (rule : SkuSubstitution) (now : Timestamp)
    (hExpired : lot.expiresAt < now) :
    serialNumbersDistinct serialized.units ∧
      ¬ lotUsableAt now lot ∧
      rule.maxSubstituteQty ≤ availableStock rule.substituteStock := by
  exact ⟨serializedInventorySet_serials_distinct serialized,
    expiredLot_not_usableAt lot now hExpired,
    skuSubstitution_max_qty_le_available rule⟩

/-- Split fulfillment keeps aggregate stock safety and proves two warehouses are involved. -/
theorem split_fulfillment_inventory_safety
    (plan : SplitFulfillmentPlan) :
    plan.plan.requested ≤ allocationsAvailableTotal plan.plan.allocations ∧
      allocationKeysDistinct plan.plan.allocations ∧
      plan.firstWarehouse.id ≠ plan.secondWarehouse.id := by
  exact ⟨splitFulfillmentPlan_requested_le_availableTotal plan,
    splitFulfillmentPlan_allocation_keys_distinct plan,
    splitFulfillmentPlan_warehouses_distinct plan⟩

/-- Safe marketplace feed lines publish prices inside their channel price policy. -/
theorem marketplace_feed_price_policy_safety (f : SafeProductFeedLine) :
    f.pricePolicy.minPrice ≤ f.price ∧ f.price ≤ f.pricePolicy.maxPrice := by
  exact f.price_valid

/-! ### Executable validator bridge theorems -/

/-- Successful executable order validation produces a pricing-safe order. -/
theorem executable_order_validation_pricing_safety
    {raw : RawOrder} {order : Order}
    (h : validateOrder raw = Except.ok order) :
    order.total ≤
      cartGrossTotal order.items + order.shippingMethod.price + order.tax := by
  exact validateOrder_sound h

/-- Successful executable feed-line validation produces a safe marketplace feed line. -/
theorem executable_feed_line_validation_safety
    {raw : RawProductFeedLine} {line : SafeProductFeedLine}
    (h : validateFeedLine raw = Except.ok line) :
    line.sku = line.stockState.sku ∧
      line.pricePolicy.minPrice ≤ line.price ∧
      line.price ≤ line.pricePolicy.maxPrice ∧
      line.stock ≤ availableStock line.stockState := by
  exact validateFeedLine_sound h

/-- Successful executable refund validation keeps refunds within remaining captured funds. -/
theorem executable_refund_validation_safety
    {raw : RawRefund} {ledger : PaymentLedger} {refund : ValidRefund}
    (h : validateRefund raw ledger = Except.ok refund) :
    refund.amount ≤ remainingRefundAmount refund.ledger := by
  exact validateRefund_sound h

/-! ### Compositional end-to-end flow theorems -/

/--
Checkout, capture, and accounting composition: a captured payment matched to an
order can be projected into a balanced journal whose totals equal the order
total, while retaining the order pricing bound.
-/
theorem checkout_to_capture_to_journal_is_safe
    (matchEvidence : CapturedPaymentMatchesOrder)
    (projection : CapturedPaymentJournalProjection)
    (hPayment : projection.payment = matchEvidence.payment) :
    matchEvidence.order.total ≤
        cartGrossTotal matchEvidence.order.items +
          matchEvidence.order.shippingMethod.price + matchEvidence.order.tax ∧
      projection.payment.orderId = matchEvidence.order.id ∧
      projection.payment.amount = matchEvidence.order.total ∧
      projection.payment.currency = matchEvidence.order.currency ∧
      debitTotal projection.journal.postings = matchEvidence.order.total ∧
      creditTotal projection.journal.postings = matchEvidence.order.total ∧
      debitTotal projection.journal.postings =
        creditTotal projection.journal.postings := by
  have hOrderSafe : matchEvidence.order.total ≤
      cartGrossTotal matchEvidence.order.items +
        matchEvidence.order.shippingMethod.price + matchEvidence.order.tax :=
    order_total_is_safe matchEvidence.order
  have hOrderId : projection.payment.orderId = matchEvidence.order.id := by
    rw [hPayment]
    exact matchEvidence.order_matches
  have hAmount : projection.payment.amount = matchEvidence.order.total := by
    rw [hPayment]
    exact matchEvidence.amount_matches
  have hCurrency : projection.payment.currency = matchEvidence.order.currency := by
    rw [hPayment]
    exact matchEvidence.currency_matches
  have hDebit : debitTotal projection.journal.postings = matchEvidence.order.total := by
    calc
      debitTotal projection.journal.postings = projection.payment.amount :=
        capturedPaymentJournalProjection_debit_amount projection
      _ = matchEvidence.order.total := hAmount
  have hCredit : creditTotal projection.journal.postings = matchEvidence.order.total := by
    calc
      creditTotal projection.journal.postings = projection.payment.amount :=
        capturedPaymentJournalProjection_credit_amount projection
      _ = matchEvidence.order.total := hAmount
  exact ⟨hOrderSafe, hOrderId, hAmount, hCurrency, hDebit, hCredit,
    capturedPaymentJournalProjection_balanced projection⟩

/--
Marketplace order, payout, and accounting composition: marketplace payout and
fee recover the internal order total, and booking the payout is balanced.
-/
theorem marketplace_order_to_payout_to_accounting_balanced
    (order : MarketplaceOrder) (accounts : AccountingAccounts) :
    order.feeLedger.payout ≤ order.internalOrder.total ∧
      order.feeLedger.payout + order.feeLedger.fee = order.internalOrder.total ∧
      debitTotal (paymentCapturedJournal accounts order.feeLedger.payout).postings =
        order.feeLedger.payout ∧
      creditTotal (paymentCapturedJournal accounts order.feeLedger.payout).postings =
        order.feeLedger.payout ∧
      debitTotal (paymentCapturedJournal accounts order.feeLedger.payout).postings =
        creditTotal (paymentCapturedJournal accounts order.feeLedger.payout).postings := by
  exact ⟨marketplaceOrder_payout_le_internal_total order,
    marketplaceOrder_payout_plus_fee_eq_internal_total order,
    paymentCapturedJournal_debitTotal accounts order.feeLedger.payout,
    paymentCapturedJournal_creditTotal accounts order.feeLedger.payout,
    paymentCapturedJournal_balanced accounts order.feeLedger.payout⟩

/--
Dropship order, supplier purchase order, and delivery composition: supplier cost
safety survives through a delivered shipment tied to the same customer order.
-/
theorem dropship_order_to_supplier_po_to_delivery_preserves_profit
    (fulfillment : DropshipFulfillment) (delivery : DeliveredShipment)
    (hOrder : delivery.promise.plan.order = fulfillment.customerOrder) :
    dropshipSupplierCostTotal fulfillment.purchaseOrder.lines ≤
        fulfillment.customerOrder.total ∧
      cartWeightTotal fulfillment.customerOrder.items ≤ delivery.promise.plan.package.weight ∧
      delivery.promise.plan.package.weight ≤
        delivery.promise.plan.quote.service.maxWeight ∧
      delivery.deliveredAt ≤ delivery.promise.plan.promisedDeliveryAt ∧
      delivery.deliveryEvent.kind = TrackingEventKind.DeliveredScan := by
  have hWeight : cartWeightTotal fulfillment.customerOrder.items ≤
      delivery.promise.plan.package.weight := by
    have h := shipmentPlan_package_covers_cart_weight delivery.promise.plan
    rw [hOrder] at h
    exact h
  exact ⟨dropshipFulfillment_supplierCost_le_orderTotal fulfillment,
    hWeight,
    shipmentPlan_package_weight_safe delivery.promise.plan,
    deliveredShipment_deliveredAt_le_plan_promised delivery,
    delivery.delivery_event_kind⟩

/--
Return authorization, physical receipt, refund, and accounting composition:
the issued refund stays within both ledger and order caps, and its journal is
balanced.
-/
theorem return_authorization_to_refund_to_journal_preserves_caps
    (receipt : ReturnReceipt) (projection : RefundJournalProjection)
    (hLedger : projection.ledger = receipt.authorization.ledger)
    (hAmount : projection.amount = receipt.refundIssued) :
    receipt.authorization.status = ReturnAuthorizationStatus.Approved ∧
      receipt.receivedQuantity ≤
        cartQuantityTotal receipt.authorization.order.items ∧
      projection.ledger = receipt.authorization.ledger ∧
      projection.amount = receipt.refundIssued ∧
      projection.amount ≤ remainingRefundAmount receipt.authorization.ledger ∧
      projection.amount ≤ receipt.authorization.order.total ∧
      debitTotal projection.journal.postings = projection.amount ∧
      creditTotal projection.journal.postings = projection.amount ∧
      debitTotal projection.journal.postings =
        creditTotal projection.journal.postings := by
  have hRemaining : projection.amount ≤
      remainingRefundAmount receipt.authorization.ledger := by
    have h := refundJournalProjection_amount_le_remaining projection
    simpa [hLedger] using h
  have hOrderCap : projection.amount ≤ receipt.authorization.order.total := by
    calc
      projection.amount = receipt.refundIssued := hAmount
      _ ≤ receipt.authorization.order.total :=
        returnReceipt_refund_le_order_total receipt
  exact ⟨returnReceipt_authorization_approved receipt,
    returnReceipt_received_le_order_quantity receipt,
    hLedger, hAmount, hRemaining, hOrderCap,
    refundJournalProjection_debit_amount projection,
    refundJournalProjection_credit_amount projection,
    refundJournalProjection_balanced projection⟩

/--
CRM outreach, order attribution, and fulfillment composition: a permitted CRM
message linked to the same CRM order keeps consent evidence, attribution bounds,
stock allocation bounds, and carrier package safety together.
-/
theorem crm_campaign_to_order_to_fulfillment_respects_consent_and_stock
    (message : PermittedAccountMessage)
    (attribution : MatchedOrderAttributionLedger)
    (shipment : ShipmentForCRMOrder)
    (hAccount : shipment.crmOrder.account = message.accountContact.account)
    (hContact : shipment.crmOrder.contact = message.accountContact.contact)
    (hOrder : attribution.ledger.order = shipment.crmOrder.order) :
    shipment.crmOrder.account = message.accountContact.account ∧
      shipment.crmOrder.contact = message.accountContact.contact ∧
      canSendMarketingMessage message.accountContact.contact.subscription ∧
      canRetarget message.accountContact.contact.retargetingConsent ∧
      dataProcessingAllowed message.accountContact.contact.dataPermission ∧
      attributionCreditTotal attribution.ledger.credits ≤
        shipment.crmOrder.order.total ∧
      shipment.plan.fulfillment.requested ≤
        allocationsAvailableTotal shipment.plan.fulfillment.allocations ∧
      shipment.plan.order.id = shipment.crmOrder.order.id ∧
      shipment.plan.package.weight ≤ shipment.plan.quote.service.maxWeight := by
  have hSubscription :
      canSendMarketingMessage message.accountContact.contact.subscription := by
    have h := permittedMessage_subscription_allowed message.message
    rw [message.message_contact_matches] at h
    exact h
  have hConsent :
      canRetarget message.accountContact.contact.retargetingConsent := by
    have h := permittedMessage_consent_allowed message.message
    rw [message.message_contact_matches] at h
    exact h
  have hProcessing :
      dataProcessingAllowed message.accountContact.contact.dataPermission :=
    permittedAccountMessage_processing_allowed message
  have hAttribution : attributionCreditTotal attribution.ledger.credits ≤
      shipment.crmOrder.order.total := by
    have h := matchedAttributionLedger_total_le_order_total attribution
    simpa [hOrder] using h
  exact ⟨hAccount, hContact, hSubscription, hConsent, hProcessing,
    hAttribution, shipmentPlan_requested_le_availableTotal shipment.plan,
    shipmentForCRMOrder_order_id_matches shipment,
    shipmentForCRMOrder_package_weight_safe shipment⟩

/-! ### Additional compositional flow families -/

/--
Catalog, feed, listing, and advertising composition: a sellable catalog entry
can be connected to a publishable feed line, an advertisable marketplace
listing, and a campaign whose destination matches that marketplace.
-/
theorem catalog_to_feed_to_advertising_is_safe
    (entry : SellableCatalogEntry)
    (feed : PublishableFeedLine)
    (listing : AdvertisableSyncedMarketplaceListing)
    (campaign : MarketingCampaign)
    (hFeedSku : feed.line.sku = entry.entry.variant.sku)
    (hListingSku : listing.synced.listing.sku = feed.line.sku)
    (hFeedChannel :
      feed.line.channel =
        SalesChannel.MarketplaceChannel listing.synced.listing.marketplace)
    (hDestination :
      destinationMatchesMarketplace
        campaign.destination listing.synced.listing.marketplace) :
    entry.entry.product.status = ProductStatus.Active ∧
      entry.entry.variant.active = true ∧
      feed.line.sku = entry.entry.variant.sku ∧
      listing.synced.listing.sku = feed.line.sku ∧
      feed.line.channel =
        SalesChannel.MarketplaceChannel listing.synced.listing.marketplace ∧
      0 < feed.line.stock ∧
      0 < availableStock feed.line.stockState ∧
      feed.line.pricePolicy.minPrice ≤ feed.line.price ∧
      feed.line.price ≤ feed.line.pricePolicy.maxPrice ∧
      listing.synced.listing.status = ListingStatus.Active ∧
      0 < listing.synced.listing.publishedStock ∧
      0 < availableStock listing.synced.stock ∧
      campaign.spend ≤ campaign.budget ∧
      destinationMatchesMarketplace
        campaign.destination listing.synced.listing.marketplace := by
  exact ⟨entry.product_active, entry.variant_active, hFeedSku, hListingSku,
    hFeedChannel, feed.has_stock, publishableFeedLine_available_positive feed,
    feed.line.price_valid.left, feed.line.price_valid.right,
    advertisableSyncedListing_active listing,
    advertisableSyncedListing_in_stock listing,
    advertisableSyncedListing_available_positive listing,
    campaign.spend_le_budget, hDestination⟩

/--
Inventory allocation through delivery tracking: allocation stock bounds,
carrier package bounds, handoff chronology, tracking identity, and delivery
promise evidence compose for one shipment flow.
-/
theorem allocation_to_delivery_tracking_is_safe
    (plan : LogisticsShipmentPlan)
    (handoff : CarrierHandoff)
    (history : TrackingHistory)
    (delivery : DeliveredShipment)
    (hHandoffPlan : handoff.plan = plan)
    (hDeliveryPlan : delivery.promise.plan = plan)
    (hHistoryShipment : history.shipmentId = plan.id)
    (hDeliveryHistory : delivery.history = history) :
    plan.fulfillment.requested ≤ allocationsAvailableTotal plan.fulfillment.allocations ∧
      allocationKeysDistinct plan.fulfillment.allocations ∧
      plan.package.weight ≤ plan.quote.service.maxWeight ∧
      plan.plannedShipAt ≤ handoff.handedOffAt ∧
      handoff.handedOffAt ≤ handoff.acceptanceScanAt ∧
      trackingEventsForShipment plan.id history.events ∧
      trackingEventsForCarrier plan.quote.service.carrierId
        history.trackingNumber history.events ∧
      trackingEventIdsDistinct history.events ∧
      delivery.deliveredAt ≤ plan.promisedDeliveryAt ∧
      delivery.deliveryEvent.kind = TrackingEventKind.DeliveredScan := by
  have hPlanned : plan.plannedShipAt ≤ handoff.handedOffAt := by
    have h := carrierHandoff_plannedShip_le_handedOff handoff
    rwa [hHandoffPlan] at h
  have hCarrier : history.carrierId = plan.quote.service.carrierId := by
    have h := deliveredShipment_history_carrier_matches_quote delivery
    rwa [hDeliveryHistory, hDeliveryPlan] at h
  have hEventsForPlan : trackingEventsForShipment plan.id history.events := by
    have h := trackingHistory_events_match_shipment history
    rwa [hHistoryShipment] at h
  have hEventsForCarrier :
      trackingEventsForCarrier plan.quote.service.carrierId
        history.trackingNumber history.events := by
    have h := trackingHistory_events_match_carrier history
    rwa [hCarrier] at h
  have hDeliveredByPlan : delivery.deliveredAt ≤ plan.promisedDeliveryAt := by
    have h := deliveredShipment_deliveredAt_le_plan_promised delivery
    rwa [hDeliveryPlan] at h
  exact ⟨shipmentPlan_requested_le_availableTotal plan,
    shipmentPlan_allocation_keys_distinct plan,
    shipmentPlan_package_weight_safe plan,
    hPlanned,
    carrierHandoff_handedOff_le_acceptanceScan handoff,
    hEventsForPlan,
    hEventsForCarrier,
    trackingHistory_event_ids_distinct history,
    hDeliveredByPlan,
    delivery.delivery_event_kind⟩

/--
Ordered event streams, webhook replay, and semantic state replay compose: an
ordered stream has matching webhook step evidence, and a valid system replay
preserves stock and refund-ledger safety.
-/
theorem ordered_domain_event_stream_replay_preserves_system_safety
    (state : WebhookOrderingState)
    (stream : ValidEventStream)
    {before after : ValidSystemState} {steps : Nat}
    (hOrdered :
      streamSequencesStrictlyIncreaseFrom state.lastSequence stream.stream.events)
    (hReplay : ValidSystemReplayInSteps before after steps) :
    streamSequencesStrictlyIncrease stream.stream ∧
      stream.stream.lastSequence = eventStreamComputedLastSequence stream.stream ∧
      (∃ next : WebhookOrderingState,
        WebhookReplayInSteps state next stream.stream.events.length) ∧
      after.stock.reserved ≤ after.stock.total ∧
      after.ledger.refunded ≤ after.ledger.captured := by
  rcases orderedWebhookStream_relatesInSteps
      state stream.stream.events hOrdered with ⟨next, hWebhook⟩
  have hState := validSystemReplayInSteps_preserves_validity hReplay
  exact ⟨stream.sequences_strict, stream.lastSequence_correct,
    ⟨next, hWebhook⟩, hState.left, hState.right⟩

/--
Lead conversion, sales pipeline, and opportunity portfolio composition:
converted lead identity and amount bounds combine with pipeline valuation and
portfolio capital/profit safety.
-/
theorem converted_lead_to_pipeline_to_portfolio_value_safe
    (conversion : ConvertedLeadOpportunity)
    (pipeline : SalesPipeline)
    (portfolio : DropshipOpportunityPortfolio)
    (hOpportunityMem : conversion.opportunity ∈ pipeline.opportunities) :
    conversion.lead.status = LeadStatus.Converted ∧
      conversion.opportunity.sourceLead = some conversion.lead.id ∧
      conversion.opportunity.amount ≤ conversion.lead.estimatedValue ∧
      conversion.opportunity ∈ pipeline.opportunities ∧
      opportunitiesUseCurrency pipeline.currency pipeline.opportunities ∧
      opportunityWeightedValueTotal pipeline.opportunities ≤
        opportunityGrossValue pipeline.opportunities ∧
      candidatesCapitalTotal portfolio.selected ≤ portfolio.investmentFund ∧
      candidatesMinProfitTotal portfolio.selected ≤
        candidatesProfitTotal portfolio.selected := by
  exact ⟨conversion.lead_converted, conversion.opportunity_source_matches,
    conversion.opportunity_amount_le_estimate, hOpportunityMem,
    pipeline.currency_consistent,
    salesPipeline_weightedValue_le_grossValue pipeline,
    opportunityPortfolio_capital_safe portfolio,
    opportunityPortfolio_expectedProfit_covers_minProfit portfolio⟩

/--
Trusted competitor signal through MAP-compliant offer and selected portfolio
candidate: freshness, trust, MAP, profit floor, competitive target price, and
portfolio bounds compose.
-/
theorem trusted_competitor_signal_to_portfolio_candidate_safe
    (benchmark : TrustedFreshCompetitorBenchmark)
    (offer : MapCompliantCompetitorAwareOffer)
    (candidate : DropshipOpportunityCandidate)
    (portfolio : DropshipOpportunityPortfolio)
    (hCandidateMem : candidate ∈ portfolio.selected) :
    benchmark.benchmark.bestOffer.observedAt ≤ benchmark.now ∧
      timestampAge benchmark.now benchmark.benchmark.bestOffer.observedAt ≤
        benchmark.maxAge ∧
      trustAllowsAutoRepricing benchmark.trust ∧
      offer.policy.mapPrice ≤ offer.offer.offer.saleUnitPrice ∧
      offer.offer.minProfit ≤
        profitAtOfferPrice offer.offer.offer.saleUnitPrice
          offer.offer.discount offer.offer.costs ∧
      candidate ∈ portfolio.selected ∧
      candidate.minProfit ≤
        profitAtOfferPrice candidate.targetPrice 0 candidate.costs ∧
      candidate.targetPrice ≤ candidate.competitorPrice ∧
      candidatesCapitalTotal portfolio.selected ≤ portfolio.investmentFund ∧
      candidatesMinProfitTotal portfolio.selected ≤
        candidatesProfitTotal portfolio.selected := by
  exact ⟨benchmark.fresh_best_offer.left, benchmark.fresh_best_offer.right,
    benchmark.trust_allows_auto, offer.advertised_ok,
    competitorAwareDropshipOffer_profit_guaranteed offer.offer,
    hCandidateMem, candidate_targetPrice_profit_safe candidate,
    candidate_targetPrice_competitive candidate,
    opportunityPortfolio_capital_safe portfolio,
    opportunityPortfolio_expectedProfit_covers_minProfit portfolio⟩

/--
Forecast, supplier quality, capacity, and distributor sourcing composition:
actionable demand can be paired with an approved supplier, capacity check, and
sourceable distributor product.
-/
theorem forecast_to_supplier_sourcing_is_safe
    (forecast : ActionableDemandForecast)
    (supplier : ApprovedOrderableSupplierQuality)
    (capacity : SupplierDailyCapacity)
    (source : SourceableDistributorProduct)
    (newOrders : Nat)
    (hCapacity : canAddSupplierOrders capacity newOrders)
    (hCapacitySupplier :
      capacity.supplier.id = supplier.quality.supplier.id)
    (hSourceSupplier :
      source.product.distributorId = supplier.quality.supplier.id)
    (hSourceSku : forecast.forecast.sku = source.product.sku) :
    confidenceAllowsAutoReplenish forecast.forecast.confidence ∧
      0 < forecast.forecast.expectedUnits ∧
      0 < forecast.forecast.horizonDays ∧
      supplier.quality.supplier.active = true ∧
      supplier.quality.supplier.suspended = false ∧
      capacity.ordersAcceptedToday + newOrders ≤ capacity.supplier.maxDailyOrders ∧
      capacity.supplier.id = supplier.quality.supplier.id ∧
      source.product.distributorId = supplier.quality.supplier.id ∧
      forecast.forecast.sku = source.product.sku ∧
      source.product.active = true ∧
      source.product.minOrderQty ≤ source.units ∧
      source.units ≤ source.product.availableQty := by
  exact ⟨forecast.actionable.left, forecast.actionable.right.left,
    forecast.actionable.right.right,
    supplier.can_receive_orders.left, supplier.can_receive_orders.right,
    canAddSupplierOrders_keeps_supplier_max capacity newOrders hCapacity,
    hCapacitySupplier, hSourceSupplier, hSourceSku,
    source.can_source.left, source.can_source.right.left,
    source.can_source.right.right⟩

/--
Retention, promotion, coupon, and order-pricing composition: CRM value guards,
promotion caps, coupon conservation, and order pricing safety compose.
-/
theorem retention_promotion_to_order_discount_is_safe
    (offer : RetentionOffer)
    (promotion : AcceptedPromotionSet)
    (application : BoundedCouponApplication)
    (order : Order)
    (hCoupon : application.coupon = offer.coupon)
    (hOrderCoupon : order.couponAmount = application.coupon.amount) :
    offer.account.status = CRMAccountStatus.Active ∧
      offer.discount ≤ offer.account.lifetimeValue ∧
      offer.discount ≤ offer.segment.maxRetentionDiscount ∧
      promotion.profitFloor ≤ promotion.resultingPrice ∧
      promotion.totalDiscount ≤ promotion.discountCap ∧
      application.coupon.amount ≤ application.subtotal ∧
      subtotalAfterCouponAmount application.subtotal application.coupon.amount +
        application.coupon.amount = application.subtotal ∧
      application.coupon = offer.coupon ∧
      order.couponAmount = application.coupon.amount ∧
      order.total ≤
        cartGrossTotal order.items + order.shippingMethod.price + order.tax := by
  exact ⟨offer.account_active,
    retentionOffer_discount_le_lifetimeValue offer,
    retentionOffer_discount_le_segment_cap offer,
    promotion.floor_le_price,
    promotion.discount_le_cap,
    application.amount_le_subtotal,
    boundedCoupon_subtotalAfter_add_amount_eq_subtotal application,
    hCoupon, hOrderCoupon,
    order_total_is_safe order⟩

/--
Gift-card redemption, chargeback, and cashflow composition: post-purchase
adjustments retain expiry/balance/chargeback caps while the cashflow plan keeps
its reserve safety.
-/
theorem post_purchase_adjustments_to_cashflow_plan_safe
    (redemption : ValidGiftCardRedemptionAt)
    (chargeback : ChargebackForCapturedPayment)
    (plan : EventBackedCashflowPlan) :
    redemption.now ≤ redemption.redemption.card.expiresAt ∧
      giftCardBalanceAfterRedeem redemption.redemption +
        redemption.redemption.amount =
          redemption.redemption.card.balance ∧
      chargeback.chargeback.chargebackAmount ≤ chargeback.payment.amount ∧
      plan.requiredReserve + cashflowOutflowsTotal plan.events ≤
        plan.startingCash + cashflowInflowsTotal plan.events := by
  exact ⟨redemption.not_expired,
    giftCardBalanceAfterRedeem_add_amount_eq_balance redemption.redemption,
    chargebackForCapturedPayment_amount_safe chargeback,
    eventBackedCashflowPlan_safe plan⟩

/--
Logistics exception through CRM support resolution: shipment/order linkage,
escalation evidence, exception chronology, and support SLA resolution compose.
-/
theorem logistics_exception_to_support_resolution_sla_safe
    (escalation : LogisticsExceptionSupportCase)
    (resolution : ResolvedSupportCase)
    (hResolvedCase : resolution.case_.id = escalation.supportCase.id) :
    escalation.exception.shipmentId = escalation.shipment.id ∧
      escalation.supportCase.orderId = some escalation.shipment.order.id ∧
      escalation.supportCase.status = SupportCaseStatus.Escalated ∧
      escalation.exception.raisedAt ≤ escalation.supportCase.openedAt ∧
      resolution.case_.id = escalation.supportCase.id ∧
      resolution.case_.openedAt ≤ resolution.resolvedAt ∧
      resolution.case_.lastUpdatedAt ≤ resolution.resolvedAt ∧
      resolution.resolvedAt ≤ resolution.case_.slaDueAt ∧
      resolution.case_.status = SupportCaseStatus.Resolved := by
  exact ⟨escalation.exception_shipment_matches,
    escalation.support_case_order_matches,
    escalation.support_case_escalated,
    escalation.exception_raised_before_case_opened,
    hResolvedCase,
    resolution.opened_le_resolved,
    resolution.lastUpdated_le_resolved,
    resolution.resolved_by_sla,
    resolution.status_resolved⟩

/--
Audited command through domain-event replay: command permission and audit log
identity compose with event-replay preservation of stock and refund-ledger
safety.
-/
theorem audited_command_to_event_replay_preserves_permission_and_state
    (cmd : AuditedCommand)
    {event : DomainEvent} {before after : ValidSystemState}
    (hStep : ValidDomainEventStep event before after) :
    CanPerform cmd.actor cmd.action ∧
      cmd.event.actor = cmd.actor ∧
      cmd.event.action = cmd.action ∧
      cmd.event.orderId = cmd.orderId ∧
      after.stock.reserved ≤ after.stock.total ∧
      after.ledger.refunded ≤ after.ledger.captured := by
  have hValid := validDomainEventStep_preserves_validity hStep
  exact ⟨cmd.allowed, cmd.event_actor_matches, cmd.event_action_matches,
    cmd.event_order_matches, hValid.left, hValid.right⟩

/-- FX floor-rounding error is bounded by one target minor unit. -/
theorem fx_floor_rounding_error_safety
    (amount : Money) (rate : ExchangeRate) :
    floorRoundingRemainder (amount * rate.numerator) rate.denominator <
      rate.denominator := by
  exact convertMoneyFloor_rounding_error_lt_one_minor_unit amount rate

/-- Tax floor-rounding error is bounded by one minor unit. -/
theorem tax_floor_rounding_error_safety
    (rate : TaxRate) (taxableAmount : Money) :
    floorRoundingRemainder (taxableAmount * rate.bps.value) 10000 < 10000 := by
  exact tax_floor_rounding_error_lt_one_minor_unit rate taxableAmount

/-- Marketplace-fee floor-rounding error is bounded by one minor unit. -/
theorem marketplace_fee_rounding_error_safety
    (gross : Money) (feeRate : BasisPoints) :
    floorRoundingRemainder (gross * feeRate.value) 10000 < 10000 := by
  exact marketplaceFee_floor_rounding_error_lt_one_minor_unit gross feeRate

/-- Marketplace-payout floor-rounding error is bounded by one minor unit. -/
theorem marketplace_payout_rounding_error_safety
    (gross : Money) (payoutRate : BasisPoints) :
    floorRoundingRemainder (gross * payoutRate.value) 10000 < 10000 := by
  exact marketplacePayout_floor_rounding_error_lt_one_minor_unit gross payoutRate

/-! ### Tax, VAT/GST, and invoicing theorems -/

/-- Tax invoice totals conserve subtotal, tax, shipping, and discount. -/
theorem tax_invoice_total_conservation
    (invoice : TaxInvoice) :
    invoice.subtotal + invoice.tax + invoice.shipping - invoice.discount =
      invoice.total := by
  exact invoice_total_conserves_components invoice

/-- Adding the bounded discount back recovers the invoice component total. -/
theorem tax_invoice_discount_conservation
    (invoice : TaxInvoice) :
    invoice.total + invoice.discount =
      invoice.subtotal + invoice.tax + invoice.shipping := by
  exact invoice_total_add_discount_eq_components invoice

/-- Tax invoices expose subtotal and tax totals as sums over invoice lines. -/
theorem tax_invoice_line_totals_match
    (invoice : TaxInvoice) :
    invoice.subtotal = invoiceLineSubtotalTotal invoice.lines ∧
      invoice.tax = invoiceLineTaxTotal invoice.lines ∧
      invoice.total ≤ invoice.subtotal + invoice.tax + invoice.shipping := by
  exact ⟨taxInvoice_subtotal_matches_lines invoice,
    taxInvoice_tax_matches_lines invoice,
    taxInvoice_total_le_components invoice⟩

/-- Tax-inclusive and tax-exclusive prices both conserve net and tax components. -/
theorem tax_price_component_conservation
    (inclusive : TaxInclusivePrice) (exclusive : TaxExclusivePrice) :
    inclusive.net + inclusive.tax = inclusive.gross ∧
      exclusive.net + exclusive.tax = exclusive.total := by
  exact ⟨taxInclusivePrice_conserves_components inclusive,
    taxExclusivePrice_conserves_components exclusive⟩

/-- Exempt, zero-rated, and reverse-charge treatments collect no seller-side tax. -/
theorem non_taxable_treatments_collect_zero_seller_tax
    (mode : RoundingMode) (rate : TaxRate) (taxableAmount : Money) :
    taxForTreatment TaxTreatment.Exempt mode rate taxableAmount = 0 ∧
      taxForTreatment TaxTreatment.ZeroRated mode rate taxableAmount = 0 ∧
      taxForTreatment TaxTreatment.ReverseCharge mode rate taxableAmount = 0 ∧
      ¬ sellerCollectsTaxForTreatment TaxTreatment.ReverseCharge := by
  exact ⟨exempt_taxForTreatment_zero mode rate taxableAmount,
    zeroRated_taxForTreatment_zero mode rate taxableAmount,
    reverseCharge_taxForTreatment_zero mode rate taxableAmount,
    reverseCharge_treatment_has_no_seller_collection⟩

/-- B2B exemption certificates prove customer, jurisdiction, validity, and zero tax. -/
theorem b2b_tax_exemption_certificate_safety
    (exemption : B2BTaxExemption)
    (mode : RoundingMode) (rate : TaxRate) (taxableAmount : Money) :
    exemption.certificate.customerId = exemption.customer.id ∧
      exemption.certificate.jurisdictionId = exemption.jurisdiction.id ∧
      exemption.customer.wholesaleApproved = true ∧
      exemption.checkedAt ≤ exemption.certificate.validUntil ∧
      taxForTreatment TaxTreatment.Exempt mode rate taxableAmount = 0 := by
  exact ⟨exemption.customer_matches, exemption.jurisdiction_matches,
    b2bTaxExemption_wholesale_approved exemption,
    b2bTaxExemption_certificate_not_expired exemption,
    (b2bExemption_collects_zero_tax exemption mode rate taxableAmount).right⟩

/-- Marketplace-facilitator tax exposes rounding and zero seller due when collected. -/
theorem marketplace_facilitator_tax_safety
    (tax : MarketplaceFacilitatorTax)
    (hCollects : tax.facilitatorCollects = true) :
    tax.tax = taxAmountRounded tax.roundingMode tax.rate tax.taxableAmount ∧
      tax.sellerTaxDue = 0 := by
  exact ⟨marketplaceFacilitatorTax_uses_declared_rounding tax,
    marketplaceFacilitator_collected_zero_seller_due tax hCollects⟩

/-- Invoice lines conserve taxable amount and tax, with bounded floor rounding error. -/
theorem tax_invoice_line_rounding_and_total_safety
    (line : TaxInvoiceLine) :
    line.tax = taxForTreatment line.treatment line.roundingMode line.rate line.taxableAmount ∧
      line.taxableAmount + line.tax = line.total ∧
      floorRoundingRemainder
        (line.taxableAmount * line.rate.bps.value) 10000 < 10000 := by
  exact ⟨line.tax_correct, taxInvoiceLine_total_conserves_components line,
    invoiceLine_floor_tax_rounding_error_lt_one_minor_unit line⟩

/-- Bounded coupon applications conserve subtotal after applying the discount amount. -/
theorem bounded_coupon_application_conservation
    (application : BoundedCouponApplication) :
    subtotalAfterCouponAmount application.subtotal application.coupon.amount +
      application.coupon.amount = application.subtotal := by
  exact boundedCoupon_subtotalAfter_add_amount_eq_subtotal application

/-- Captured payments validated against an order match id, amount, and currency. -/
theorem captured_payment_order_match_safety
    (matchEvidence : CapturedPaymentMatchesOrder) :
    matchEvidence.payment.orderId = matchEvidence.order.id ∧
      matchEvidence.payment.amount = matchEvidence.order.total ∧
      matchEvidence.payment.currency = matchEvidence.order.currency := by
  exact ⟨matchEvidence.order_matches, matchEvidence.amount_matches, matchEvidence.currency_matches⟩

/-- Valid event streams keep strict sequence ordering and a correct cursor. -/
theorem valid_event_stream_cursor_safety
    (stream : ValidEventStream) :
    streamSequencesStrictlyIncrease stream.stream ∧
      stream.stream.lastSequence = eventStreamComputedLastSequence stream.stream := by
  exact ⟨stream.sequences_strict, stream.lastSequence_correct⟩

/-- Sellable catalog entries pair a matching variant with active product and variant state. -/
theorem sellable_catalog_entry_safety
    (entry : SellableCatalogEntry) :
    entry.entry.variant.productId = entry.entry.product.id ∧
      entry.entry.product.status = ProductStatus.Active ∧
      entry.entry.variant.active = true := by
  exact ⟨entry.entry.variant_belongs_to_product, entry.product_active, entry.variant_active⟩

/-- Publishable feed lines have stock, source stock available, and valid channel pricing. -/
theorem publishable_feed_line_safety
    (line : PublishableFeedLine) :
    0 < line.line.stock ∧
      0 < availableStock line.line.stockState ∧
      line.line.pricePolicy.minPrice ≤ line.line.price ∧
      line.line.price ≤ line.line.pricePolicy.maxPrice := by
  exact ⟨line.has_stock, publishableFeedLine_available_positive line,
    line.line.price_valid.left, line.line.price_valid.right⟩

/-- Validated experiment variants cannot claim more than the experiment's 100% traffic pool. -/
theorem experiment_variant_weight_safety
    (experiment : Experiment) (variant : ExperimentVariant)
    (hmem : variant ∈ experiment.variants) :
    variant.trafficWeight ≤ 100 := by
  exact experimentVariant_trafficWeight_le_100 experiment variant hmem

/-- Sourceable distributor products are active and fit min/max quantity constraints. -/
theorem sourceable_distributor_product_safety
    (source : SourceableDistributorProduct) :
    source.product.active = true ∧
      source.product.minOrderQty ≤ source.units ∧
      source.units ≤ source.product.availableQty := by
  exact ⟨source.can_source.left, source.can_source.right.left, source.can_source.right.right⟩

/-- Fraud-checked coupon applications satisfy both coupon and fraud-policy usage caps. -/
theorem fraud_checked_coupon_application_safety
    (application : FraudCheckedCouponApplication) :
    application.application.usesBefore ≤ application.policy.maxCouponUses ∧
      application.application.usesBefore < application.application.coupon.maxUses := by
  exact ⟨application.uses_allowed, application.application.applicable.right⟩

/-- Captured-payment journal projections balance and use the captured amount on both sides. -/
theorem captured_payment_journal_projection_safety
    (projection : CapturedPaymentJournalProjection) :
    debitTotal projection.journal.postings = projection.payment.amount ∧
      creditTotal projection.journal.postings = projection.payment.amount ∧
      debitTotal projection.journal.postings =
        creditTotal projection.journal.postings := by
  exact ⟨capturedPaymentJournalProjection_debit_amount projection,
    capturedPaymentJournalProjection_credit_amount projection,
    capturedPaymentJournalProjection_balanced projection⟩

/-- Refund journal projections balance, use the refund amount, and fit remaining balance. -/
theorem refund_journal_projection_safety
    (projection : RefundJournalProjection) :
    debitTotal projection.journal.postings = projection.amount ∧
      creditTotal projection.journal.postings = projection.amount ∧
      debitTotal projection.journal.postings =
        creditTotal projection.journal.postings ∧
      projection.amount ≤ remainingRefundAmount projection.ledger := by
  exact ⟨refundJournalProjection_debit_amount projection,
    refundJournalProjection_credit_amount projection,
    refundJournalProjection_balanced projection,
    refundJournalProjection_amount_le_remaining projection⟩

/-! ### Realistic accounting theorems -/

/-- Accrual invoices balance receivables against revenue and tax liability. -/
theorem accrual_invoice_accounting_safety
    (accounts : AdvancedAccountingAccounts)
    (subtotal tax total : Money)
    (hTotal : total = subtotal + tax) :
    debitTotal (invoiceAccrualJournal accounts subtotal tax total hTotal).postings =
        creditTotal (invoiceAccrualJournal accounts subtotal tax total hTotal).postings ∧
      debitTotal (invoiceAccrualJournal accounts subtotal tax total hTotal).postings = total ∧
      creditTotal (invoiceAccrualJournal accounts subtotal tax total hTotal).postings =
        subtotal + tax ∧
      tax ≤ creditTotal (invoiceAccrualJournal accounts subtotal tax total hTotal).postings := by
  exact ⟨invoiceAccrualJournal_balanced accounts subtotal tax total hTotal,
    invoiceAccrualJournal_debitTotal accounts subtotal tax total hTotal,
    invoiceAccrualJournal_creditTotal accounts subtotal tax total hTotal,
    invoiceAccrualJournal_tax_le_creditTotal accounts subtotal tax total hTotal⟩

/-- Cash sales balance cash against revenue and tax liability. -/
theorem cash_sale_accounting_safety
    (accounts : AdvancedAccountingAccounts)
    (subtotal tax total : Money)
    (hTotal : total = subtotal + tax) :
    debitTotal (cashSaleJournal accounts subtotal tax total hTotal).postings =
      creditTotal (cashSaleJournal accounts subtotal tax total hTotal).postings := by
  exact cashSaleJournal_balanced accounts subtotal tax total hTotal

/-- Accounts receivable and payable operational journals are balanced. -/
theorem receivable_payable_accounting_safety
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    debitTotal (receivableCollectionJournal accounts amount).postings =
        creditTotal (receivableCollectionJournal accounts amount).postings ∧
      debitTotal (supplierBillJournal accounts amount).postings =
        creditTotal (supplierBillJournal accounts amount).postings ∧
      debitTotal (supplierPaymentJournal accounts amount).postings =
        creditTotal (supplierPaymentJournal accounts amount).postings := by
  exact ⟨receivableCollectionJournal_balanced accounts amount,
    supplierBillJournal_balanced accounts amount,
    supplierPaymentJournal_balanced accounts amount⟩

/-- Marketplace clearing settlement conserves gross sales across payout and fees. -/
theorem marketplace_clearing_settlement_accounting_safety
    (accounts : AdvancedAccountingAccounts)
    (gross fee payout : Money)
    (hSettlement : payout + fee = gross) :
    debitTotal (marketplaceSettlementJournal accounts gross fee payout hSettlement).postings =
        gross ∧
      debitTotal (marketplaceSettlementJournal accounts gross fee payout hSettlement).postings =
        creditTotal
          (marketplaceSettlementJournal accounts gross fee payout hSettlement).postings := by
  exact ⟨marketplaceSettlementJournal_debitTotal_eq_gross
      accounts gross fee payout hSettlement,
    marketplaceSettlementJournal_balanced accounts gross fee payout hSettlement⟩

/-- Marketplace orders can be settled through the clearing account without imbalance. -/
theorem marketplace_order_clearing_settlement_accounting_safety
    (order : MarketplaceOrder) (accounts : AdvancedAccountingAccounts) :
    debitTotal
        (marketplaceSettlementJournal
          accounts order.internalOrder.total order.feeLedger.fee order.feeLedger.payout
          (marketplaceOrder_payout_plus_fee_eq_internal_total order)).postings =
        order.internalOrder.total ∧
      debitTotal
        (marketplaceSettlementJournal
          accounts order.internalOrder.total order.feeLedger.fee order.feeLedger.payout
          (marketplaceOrder_payout_plus_fee_eq_internal_total order)).postings =
        creditTotal
          (marketplaceSettlementJournal
            accounts order.internalOrder.total order.feeLedger.fee order.feeLedger.payout
            (marketplaceOrder_payout_plus_fee_eq_internal_total order)).postings := by
  exact marketplace_clearing_settlement_accounting_safety
    accounts order.internalOrder.total order.feeLedger.fee order.feeLedger.payout
    (marketplaceOrder_payout_plus_fee_eq_internal_total order)

/--
Full marketplace payout reconciliation conserves gross sales across payout,
fees, refunds, reserves, and tax withholding.
-/
theorem marketplace_payout_reconciliation_accounting_safety
    (accounts : AdvancedAccountingAccounts)
    (gross fee refund reserve tax payout : Money)
    (hReconciles : payout + fee + refund + reserve + tax = gross) :
    debitTotal
        (marketplacePayoutReconciliationJournal
          accounts gross fee refund reserve tax payout hReconciles).postings =
        gross ∧
      debitTotal
        (marketplacePayoutReconciliationJournal
          accounts gross fee refund reserve tax payout hReconciles).postings =
        creditTotal
          (marketplacePayoutReconciliationJournal
            accounts gross fee refund reserve tax payout hReconciles).postings := by
  exact ⟨marketplacePayoutReconciliationJournal_debitTotal_eq_gross
      accounts gross fee refund reserve tax payout hReconciles,
    marketplacePayoutReconciliationJournal_balanced
      accounts gross fee refund reserve tax payout hReconciles⟩

/-- Chargeback reserve accrual and settlement journals remain balanced. -/
theorem chargeback_reserve_accounting_safety
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    debitTotal (chargebackReserveJournal accounts amount).postings =
        creditTotal (chargebackReserveJournal accounts amount).postings ∧
      debitTotal (chargebackSettlementJournal accounts amount).postings =
        creditTotal (chargebackSettlementJournal accounts amount).postings := by
  exact ⟨chargebackReserveJournal_balanced accounts amount,
    chargebackSettlementJournal_balanced accounts amount⟩

/-- Realized and unrealized FX gain/loss journals remain double-entry balanced. -/
theorem fx_revaluation_accounting_safety
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    debitTotal (unrealizedFxGainJournal accounts amount).postings =
        creditTotal (unrealizedFxGainJournal accounts amount).postings ∧
      debitTotal (unrealizedFxLossJournal accounts amount).postings =
        creditTotal (unrealizedFxLossJournal accounts amount).postings ∧
      debitTotal (realizedFxGainJournal accounts amount).postings =
        creditTotal (realizedFxGainJournal accounts amount).postings ∧
      debitTotal (realizedFxLossJournal accounts amount).postings =
        creditTotal (realizedFxLossJournal accounts amount).postings := by
  exact fxRevaluationJournals_balanced accounts amount

/-- Advertisable synced listings are active, publish stock, and have source stock available. -/
theorem advertisable_synced_listing_safety
    (listing : AdvertisableSyncedMarketplaceListing) :
    listing.synced.listing.status = ListingStatus.Active ∧
      0 < listing.synced.listing.publishedStock ∧
      0 < availableStock listing.synced.stock := by
  exact ⟨advertisableSyncedListing_active listing,
    advertisableSyncedListing_in_stock listing,
    advertisableSyncedListing_available_positive listing⟩

/-- Wholesale credit checkouts prove customer eligibility, credit safety, and price bounds. -/
theorem wholesale_credit_checkout_safety
    (checkout : WholesaleCreditCheckout) :
    customerCanBuyWholesale checkout.account.customer ∧
      checkout.account.outstanding + checkout.orderTotal ≤ checkout.account.creditLimit ∧
      wholesaleOrderNetTotal checkout.lines ≤ wholesaleRetailEquivalentTotal checkout.lines := by
  exact ⟨wholesaleCreditCheckout_customer_can_buy checkout,
    wholesaleCreditCheckout_credit_safe checkout,
    wholesaleCreditCheckout_net_le_retail_equivalent checkout⟩

/-- Trusted fresh competitor benchmarks are relevant, fresh, and allowed for repricing. -/
theorem trusted_fresh_competitor_benchmark_safety
    (benchmark : TrustedFreshCompetitorBenchmark) :
    benchmark.benchmark.bestOffer.observedAt ≤ benchmark.now ∧
      timestampAge benchmark.now benchmark.benchmark.bestOffer.observedAt ≤ benchmark.maxAge ∧
      competitorOfferRelevant
        benchmark.benchmark.bestOffer benchmark.benchmark.sku benchmark.benchmark.currency ∧
      trustAllowsAutoRepricing benchmark.trust := by
  exact ⟨benchmark.fresh_best_offer.left, benchmark.fresh_best_offer.right,
    benchmark.benchmark.bestOffer_relevant, benchmark.trust_allows_auto⟩

/-- MAP-compliant competitor-aware offers retain both MAP and profit guarantees. -/
theorem map_compliant_competitor_offer_safety
    (offer : MapCompliantCompetitorAwareOffer) :
    offer.policy.mapPrice ≤ offer.offer.offer.saleUnitPrice ∧
      offer.offer.minProfit ≤
        profitAtOfferPrice offer.offer.offer.saleUnitPrice offer.offer.discount offer.offer.costs := by
  exact ⟨offer.advertised_ok, competitorAwareDropshipOffer_profit_guaranteed offer.offer⟩

/-- Fresh currency conversions prove source/target currency, computed amount, and quote freshness. -/
theorem fresh_currency_conversion_safety
    (conversion : FreshCurrencyConversion) :
    conversion.sourceAmount.currency = conversion.rate.source ∧
      conversion.targetAmount.currency = conversion.rate.target ∧
      conversion.targetAmount.amount =
        convertMoneyFloor conversion.sourceAmount.amount conversion.rate ∧
      conversion.rate.observedAt ≤ conversion.now ∧
      timestampAge conversion.now conversion.rate.observedAt ≤ conversion.maxAge := by
  exact ⟨conversion.source_matches_rate, conversion.target_matches_rate,
    conversion.amount_correct, conversion.rate_fresh.left, conversion.rate_fresh.right⟩

/-- Time-valid gift-card redemptions prove expiry safety and balance conservation. -/
theorem valid_gift_card_redemption_at_safety
    (redemption : ValidGiftCardRedemptionAt) :
    redemption.now ≤ redemption.redemption.card.expiresAt ∧
      giftCardBalanceAfterRedeem redemption.redemption + redemption.redemption.amount =
        redemption.redemption.card.balance := by
  exact ⟨redemption.not_expired,
    giftCardBalanceAfterRedeem_add_amount_eq_balance redemption.redemption⟩

/-- Chargebacks linked to captured payments cannot exceed the captured amount. -/
theorem chargeback_for_captured_payment_safety
    (chargeback : ChargebackForCapturedPayment) :
    chargeback.chargeback.chargebackAmount ≤ chargeback.payment.amount := by
  exact chargebackForCapturedPayment_amount_safe chargeback

/-- Actionable demand forecasts have confidence, positive demand, and a positive horizon. -/
theorem actionable_demand_forecast_safety
    (forecast : ActionableDemandForecast) :
    confidenceAllowsAutoReplenish forecast.forecast.confidence ∧
      0 < forecast.forecast.expectedUnits ∧
      0 < forecast.forecast.horizonDays := by
  exact forecast.actionable

/-- Approved orderable suppliers satisfy quality thresholds and are active/not suspended. -/
theorem approved_orderable_supplier_quality_safety
    (supplier : ApprovedOrderableSupplierQuality) :
    supplier.quality.metrics.defectRateBps ≤ supplier.quality.policy.maxDefectRateBps ∧
      supplier.quality.metrics.lateShipmentRateBps ≤
        supplier.quality.policy.maxLateShipmentRateBps ∧
      supplier.quality.metrics.cancellationRateBps ≤
        supplier.quality.policy.maxCancellationRateBps ∧
      supplier.quality.supplier.active = true ∧
      supplier.quality.supplier.suspended = false := by
  exact ⟨supplier.quality.defect_ok, supplier.quality.late_ok,
    supplier.quality.cancellation_ok, supplier.can_receive_orders.left,
    supplier.can_receive_orders.right⟩

/-- Valid search results are not archived, are in stock, and are margin-safe. -/
theorem merchandising_search_result_safety (x : ValidSearchResultItem) :
    x.item.archived = false ∧ x.item.inStock = true ∧ x.item.marginSafe = true := by
  exact validSearchResult_safe x

/-- Gift-card redemption conserves the original balance across remaining balance and redemption. -/
theorem gift_card_redemption_conservation (r : GiftCardRedemption) :
    giftCardBalanceAfterRedeem r + r.amount = r.card.balance := by
  exact giftCardBalanceAfterRedeem_add_amount_eq_balance r

/-- Strictly ordered webhook streams replay without hitting an ordering rejection. -/
theorem ordered_webhook_replay_succeeds
    (s : WebhookOrderingState) (events : List EventEnvelope)
    (h : streamSequencesStrictlyIncreaseFrom s.lastSequence events) :
    ∃ next : WebhookOrderingState, replayWebhookStream s events = some next := by
  exact replayWebhookStream_succeeds_of_ordered s events h

/-- Supplier capacity checks remain bounded by the supplier's configured maximum. -/
theorem supplier_capacity_safety (capacity : SupplierDailyCapacity) :
    capacity.ordersAcceptedToday ≤ capacity.supplier.maxDailyOrders := by
  exact supplierDailyCapacity_accepted_le_supplier_max capacity

/-- CSLib reachability for the normal paid order workflow. -/
theorem order_workflow_paid_path_reaches_delivered :
    orderStatusLTS.CanReach OrderStatus.New OrderStatus.Delivered := by
  exact new_order_can_reach_delivered

/-- CSLib execution evidence records intermediate states for the normal order workflow. -/
theorem order_workflow_paid_path_has_execution :
    ∃ states : List OrderStatus,
      orderStatusLTS.Execution
        OrderStatus.New paidFulfillmentTrace OrderStatus.Delivered states := by
  exact paidFulfillmentTrace_has_execution

/-- CSLib trace equivalence for terminal no-outgoing order outcomes. -/
theorem order_terminal_outcomes_trace_equivalent :
    Cslib.LTS.HomTraceEq orderStatusLTS OrderStatus.Cancelled OrderStatus.Refunded := by
  exact cancelled_trace_equivalent_refunded

/-- Cancelled orders cannot transition to any later order state. -/
theorem cancelled_order_cannot_transition (next : OrderStatus) :
    ¬ CanOrderTransition OrderStatus.Cancelled next := by
  exact cancelled_has_no_outgoing next

/-- Refunded orders cannot transition to any later order state. -/
theorem refunded_order_cannot_transition (next : OrderStatus) :
    ¬ CanOrderTransition OrderStatus.Refunded next := by
  exact refunded_has_no_outgoing next

/-- Cancelled orders cannot transition directly to delivered. -/
theorem order_cancelled_cannot_transition_to_delivered :
    ¬ CanOrderTransition OrderStatus.Cancelled OrderStatus.Delivered := by
  exact cancelled_cannot_become_delivered

/-- Refunded orders cannot transition directly back to paid/captured. -/
theorem order_refunded_cannot_transition_to_paid :
    ¬ CanOrderTransition OrderStatus.Refunded OrderStatus.Paid := by
  exact refunded_cannot_become_paid

/-- Cancelled orders cannot reach delivered through any later workflow trace. -/
theorem order_cancelled_cannot_reach_delivered :
    ¬ orderStatusLTS.CanReach OrderStatus.Cancelled OrderStatus.Delivered := by
  exact cancelled_order_cannot_reach_delivered

/-- Cancelled orders cannot reach paid through any later workflow trace. -/
theorem order_cancelled_cannot_reach_paid :
    ¬ orderStatusLTS.CanReach OrderStatus.Cancelled OrderStatus.Paid := by
  exact cancelled_order_cannot_reach_paid

/-- Cancelled orders cannot reach refunded through any later workflow trace. -/
theorem order_cancelled_cannot_reach_refunded :
    ¬ orderStatusLTS.CanReach OrderStatus.Cancelled OrderStatus.Refunded := by
  exact cancelled_order_cannot_reach_refunded

/-- Refunded orders cannot be captured or paid again through any workflow trace. -/
theorem order_refunded_cannot_be_captured_again :
    ¬ orderStatusLTS.CanReach OrderStatus.Refunded OrderStatus.Paid := by
  exact refunded_order_cannot_be_captured_again

/-- Refunded orders cannot reach delivered through any later workflow trace. -/
theorem order_refunded_cannot_reach_delivered :
    ¬ orderStatusLTS.CanReach OrderStatus.Refunded OrderStatus.Delivered := by
  exact refunded_order_cannot_reach_delivered

/-- Delivered order traces from `New` must include a payment step. -/
theorem order_delivered_without_payment_unreachable
    {trace : List OrderTransitionLabel}
    (hNoCapture : OrderTransitionLabel.CapturePayment ∉ trace)
    (hNoBackorderPayment : OrderTransitionLabel.ReceiveBackorderPayment ∉ trace) :
    ¬ orderStatusLTS.MTr OrderStatus.New trace OrderStatus.Delivered := by
  exact delivered_without_paid_is_unreachable hNoCapture hNoBackorderPayment

/-- CSLib reachability for the normal dropship supplier purchase-order workflow. -/
theorem dropship_po_workflow_reaches_delivered :
    dropshipPOLTS.CanReach DropshipPOStatus.Created DropshipPOStatus.Delivered := by
  exact dropshipPO_can_reach_delivered

/-- Cancelled supplier POs cannot transition to any later PO state. -/
theorem dropship_po_cancelled_cannot_transition (next : DropshipPOStatus) :
    ¬ CanDropshipPOTransition DropshipPOStatus.Cancelled next := by
  exact dropshipPO_cancelled_has_no_outgoing next

/-- Rejected supplier POs cannot transition to any later PO state. -/
theorem dropship_po_rejected_cannot_transition (next : DropshipPOStatus) :
    ¬ CanDropshipPOTransition DropshipPOStatus.Rejected next := by
  exact dropshipPO_rejected_has_no_outgoing next

/-- Delivered supplier POs cannot transition to any later PO state. -/
theorem dropship_po_delivered_cannot_transition (next : DropshipPOStatus) :
    ¬ CanDropshipPOTransition DropshipPOStatus.Delivered next := by
  exact dropshipPO_delivered_has_no_outgoing next

/-- Cancelled supplier POs cannot transition directly to delivered. -/
theorem dropship_po_cancelled_cannot_transition_to_delivered :
    ¬ CanDropshipPOTransition DropshipPOStatus.Cancelled DropshipPOStatus.Delivered := by
  exact dropshipPO_cancelled_cannot_become_delivered

/-- Rejected supplier POs cannot transition directly to delivered. -/
theorem dropship_po_rejected_cannot_transition_to_delivered :
    ¬ CanDropshipPOTransition DropshipPOStatus.Rejected DropshipPOStatus.Delivered := by
  exact dropshipPO_rejected_cannot_become_delivered

/-- Cancelled supplier POs cannot reach delivered through any later PO trace. -/
theorem dropship_po_cancelled_cannot_reach_delivered :
    ¬ dropshipPOLTS.CanReach DropshipPOStatus.Cancelled DropshipPOStatus.Delivered := by
  exact dropshipPO_cancelled_cannot_reach_delivered

/-- Rejected supplier POs cannot reach delivered through any later PO trace. -/
theorem dropship_po_rejected_cannot_reach_delivered :
    ¬ dropshipPOLTS.CanReach DropshipPOStatus.Rejected DropshipPOStatus.Delivered := by
  exact dropshipPO_rejected_cannot_reach_delivered

/-- Delivered supplier POs cannot later become cancelled. -/
theorem dropship_po_delivered_cannot_reach_cancelled :
    ¬ dropshipPOLTS.CanReach DropshipPOStatus.Delivered DropshipPOStatus.Cancelled := by
  exact dropshipPO_delivered_cannot_reach_cancelled

/-- Delivered supplier PO traces from `Created` must include supplier acceptance. -/
theorem dropship_po_delivery_without_acceptance_unreachable
    {trace : List DropshipPOTransitionLabel}
    (hNoAccept : DropshipPOTransitionLabel.Accept ∉ trace) :
    ¬ dropshipPOLTS.MTr
      DropshipPOStatus.Created trace DropshipPOStatus.Delivered := by
  exact dropshipPO_delivery_without_acceptance_is_unreachable hNoAccept

/-- Closed CRM accounts cannot transition to any later account state. -/
theorem closed_crm_account_cannot_transition (next : CRMAccountStatus) :
    ¬ CanCRMAccountTransition CRMAccountStatus.Closed next := by
  exact closedCRMAccount_has_no_outgoing next

/-- Converted leads cannot transition to any later lead state. -/
theorem converted_lead_cannot_transition (next : LeadStatus) :
    ¬ CanLeadTransition LeadStatus.Converted next := by
  exact convertedLead_has_no_outgoing next

/-- Disqualified leads cannot transition to any later lead state. -/
theorem disqualified_lead_cannot_transition (next : LeadStatus) :
    ¬ CanLeadTransition LeadStatus.Disqualified next := by
  exact disqualifiedLead_has_no_outgoing next

/-- Won opportunities cannot transition to any later opportunity stage. -/
theorem won_opportunity_cannot_transition (next : OpportunityStage) :
    ¬ CanOpportunityTransition OpportunityStage.Won next := by
  exact wonOpportunity_has_no_outgoing next

/-- Lost opportunities cannot transition to any later opportunity stage. -/
theorem lost_opportunity_cannot_transition (next : OpportunityStage) :
    ¬ CanOpportunityTransition OpportunityStage.Lost next := by
  exact lostOpportunity_has_no_outgoing next

/-- Closed support cases cannot transition to any later support status. -/
theorem closed_support_case_cannot_transition (next : SupportCaseStatus) :
    ¬ CanSupportCaseTransition SupportCaseStatus.Closed next := by
  exact closedSupportCase_has_no_outgoing next

/-- Delivered shipments cannot transition to any later shipment status. -/
theorem delivered_shipment_cannot_transition (next : ShipmentStatus) :
    ¬ CanShipmentTransition ShipmentStatus.Delivered next := by
  exact deliveredShipmentStatus_has_no_outgoing next

/-- Cancelled shipments cannot transition to any later shipment status. -/
theorem cancelled_shipment_cannot_transition (next : ShipmentStatus) :
    ¬ CanShipmentTransition ShipmentStatus.Cancelled next := by
  exact cancelledShipmentStatus_has_no_outgoing next

/-- Returned shipments cannot transition to any later shipment status. -/
theorem returned_shipment_cannot_transition (next : ShipmentStatus) :
    ¬ CanShipmentTransition ShipmentStatus.Returned next := by
  exact returnedShipmentStatus_has_no_outgoing next

/-- Rejected return authorizations cannot transition to any later return status. -/
theorem rejected_return_authorization_cannot_transition
    (next : ReturnAuthorizationStatus) :
    ¬ CanReturnAuthorizationTransition ReturnAuthorizationStatus.Rejected next := by
  exact rejectedReturnAuthorization_has_no_outgoing next

/-- Closed return authorizations cannot transition to any later return status. -/
theorem closed_return_authorization_cannot_transition
    (next : ReturnAuthorizationStatus) :
    ¬ CanReturnAuthorizationTransition ReturnAuthorizationStatus.Closed next := by
  exact closedReturnAuthorization_has_no_outgoing next

/-- Ordered webhook streams induce a CSLib replay with one accepted step per envelope. -/
theorem ordered_webhook_replay_has_step_count
    (s : WebhookOrderingState) (events : List EventEnvelope)
    (h : streamSequencesStrictlyIncreaseFrom s.lastSequence events) :
    ∃ next : WebhookOrderingState,
      WebhookReplayInSteps s next events.length := by
  exact orderedWebhookStream_relatesInSteps s events h

/-- Bounded valid-system event replay preserves stock and ledger safety. -/
theorem valid_system_replay_preserves_safety
    {before after : ValidSystemState} {steps : Nat}
    (h : ValidSystemReplayInSteps before after steps) :
    after.stock.reserved ≤ after.stock.total ∧
      after.ledger.refunded ≤ after.ledger.captured := by
  exact validSystemReplayInSteps_preserves_validity h

/-- Event-aware domain projection steps preserve core stock and ledger safety. -/
theorem valid_domain_event_step_preserves_safety
    {event : DomainEvent} {before after : ValidSystemState}
    (h : ValidDomainEventStep event before after) :
    after.stock.reserved ≤ after.stock.total ∧
      after.ledger.refunded ≤ after.ledger.captured := by
  exact validDomainEventStep_preserves_validity h

/-- Executable semantic domain-event replay is deterministic. -/
theorem semantic_domain_event_replay_deterministic
    {state before after : ValidSystemState} {events : List DomainEvent}
    (hBefore : replayDomainEvents? state events = some before)
    (hAfter : replayDomainEvents? state events = some after) :
    before = after := by
  exact replayDomainEvents?_deterministic hBefore hAfter

/-- Duplicate idempotency keys do not apply a domain event a second time. -/
theorem duplicate_idempotency_key_noops
    (key : IdempotencyKey) (event : DomainEvent)
    (state : ValidSystemState) (idempotency : IdempotencyState)
    (hProcessed : alreadyProcessed key idempotency) :
    applyIdempotentDomainEvent? key event state idempotency =
      some (state, idempotency) := by
  exact processed_idempotency_key_noops key event state idempotency hProcessed

/-- After a successful keyed event, replaying the same key does not apply it again. -/
theorem duplicate_idempotency_key_after_success_noops
    (key : IdempotencyKey) (event : DomainEvent)
    (state after : ValidSystemState) (idempotency : IdempotencyState)
    (hFresh : ¬ alreadyProcessed key idempotency)
    (hApply : applyDomainEvent? state event = some after) :
    applyIdempotentDomainEvent?
        key event after (markProcessed key idempotency) =
      some (after, markProcessed key idempotency) := by
  exact (duplicate_idempotency_key_does_not_apply_twice
    key event state after idempotency hFresh hApply).right

/-- Independent stock-reservation and refund projections commute. -/
theorem stock_reservation_refund_projection_commutes
    (state : ValidSystemState) (sku : Sku) (quantity : Quantity)
    (refundAmount : Money)
    (hSku : state.stock.sku = sku)
    (hReserve : canReserve state.stock quantity)
    (hRefund : canRefund state.ledger refundAmount) :
    let afterReserve := applyStockReservedEvent state sku quantity hSku hReserve
    let afterRefund := applyRefundIssuedEvent state refundAmount hRefund
    applyRefundIssuedEvent afterReserve refundAmount hRefund =
      applyStockReservedEvent afterRefund sku quantity hSku hReserve := by
  exact stock_reservation_and_refund_commute
    state sku quantity refundAmount hSku hReserve hRefund

/-- CRM and logistics projections commute because they touch independent counters. -/
theorem crm_logistics_projection_commutes (state : ValidSystemState) :
    applyCRMProjectedEvent (applyLogisticsProjectedEvent state) =
      applyLogisticsProjectedEvent (applyCRMProjectedEvent state) := by
  exact crm_and_logistics_projection_commute state

/-- Replaying from a snapshot is equivalent to replaying prefix and suffix together. -/
theorem snapshot_replay_equivalence
    (state snapshotState : ValidSystemState)
    (prefix suffix : List DomainEvent) (lastSequence : Nat)
    (hPrefix : replayDomainEvents? state prefix = some snapshotState) :
    replayDomainEvents? state (prefix ++ suffix) =
      replayFromSnapshot?
        { state := snapshotState, lastSequence := lastSequence } suffix := by
  exact replay_from_snapshot_equivalent_to_full_replay
    state snapshotState prefix suffix lastSequence hPrefix

/-- Successful ledger projection equals the payment/refund event folds. -/
theorem ledger_projection_matches_payment_refund_folds
    {ledger projected : PaymentLedger} {events : List DomainEvent}
    (h : projectLedger? ledger events = some projected) :
    projected.captured = ledgerCapturedFold ledger.captured events ∧
      projected.refunded = ledgerRefundedFold ledger.refunded events := by
  exact projectLedger?_matches_payment_refund_folds h

/-- CRM projected events preserve core valid-system safety and increment the CRM counter. -/
theorem crm_projected_event_safety (state : ValidSystemState) :
    let next := applyCRMProjectedEvent state
    next.stock.reserved ≤ next.stock.total ∧
      next.ledger.refunded ≤ next.ledger.captured ∧
      next.crmEventCount = state.crmEventCount + 1 := by
  simp [applyCRMProjectedEvent]
  exact ⟨state.stock.reserved_le_total, state.ledger.refunded_le_captured⟩

/-- Logistics projected events preserve core valid-system safety and increment the logistics counter. -/
theorem logistics_projected_event_safety (state : ValidSystemState) :
    let next := applyLogisticsProjectedEvent state
    next.stock.reserved ≤ next.stock.total ∧
      next.ledger.refunded ≤ next.ledger.captured ∧
      next.logisticsEventCount = state.logisticsEventCount + 1 := by
  simp [applyLogisticsProjectedEvent]
  exact ⟨state.stock.reserved_le_total, state.ledger.refunded_le_captured⟩

/-- The coarse order-event validator accepts a regular language. -/
theorem order_event_validator_language_regular :
    (Cslib.Automata.Acceptor.language orderEventValidator).IsRegular := by
  exact orderEventValidator_language_regular

/-- Entity-scoped audited commands prove actor, action, subject, and permission evidence. -/
theorem audited_entity_command_safety
    (cmd : AuditedEntityCommand) :
    cmd.event.actor = cmd.actor ∧
      cmd.event.action = cmd.action ∧
      cmd.event.subjectId = cmd.subjectId ∧
      CanPerform cmd.actor cmd.action := by
  exact ⟨cmd.event_actor_matches, cmd.event_action_matches,
    cmd.event_subject_matches, cmd.allowed⟩

/-- CSLib `TimeM` allocation summation preserves the existing allocation safety bound. -/
theorem timed_allocation_total_safety (allocations : List Allocation) :
    (timedAllocationsTotal allocations).ret ≤ allocationsAvailableTotal allocations := by
  exact timedAllocationsTotal_le_availableTotal allocations

/-- CSLib finite-support keyed allocation totals are bounded by aggregate allocation totals. -/
theorem keyed_allocation_total_safety
    (allocations : List Allocation) (key : AllocationKey) :
    allocationQuantityByKey allocations key ≤ allocationsTotal allocations := by
  exact allocationQuantityByKey_le_total allocations key

/-- CSLib merge sort preserves the extracted opportunity ranking keys. -/
theorem opportunity_ranking_preserves_rank_keys
    (candidates : List DropshipOpportunityCandidate) :
    List.Perm (rankOpportunityKeys candidates).ret (opportunityRankKeys candidates) := by
  exact rankOpportunityKeys_perm candidates

/-- CRM pipeline weighted value is bounded by gross opportunity value. -/
theorem crm_pipeline_weighted_value_safety
    (opportunities : List SalesOpportunity) :
    opportunityWeightedValueTotal opportunities ≤ opportunityGrossValue opportunities := by
  exact opportunityWeightedValueTotal_le_grossValue opportunities

/-- Active CRM accounts expose active status and balance safety. -/
theorem active_crm_account_safety
    (account : ActiveCRMAccount) :
    account.account.status = CRMAccountStatus.Active ∧
      account.account.openBalance ≤ account.account.lifetimeValue := by
  exact ⟨account.active, account.account.openBalance_le_lifetimeValue⟩

/-- Valid CRM account/contact pairs preserve account and customer identity. -/
theorem crm_account_contact_identity_safety
    (x : CRMAccountContact) :
    x.contact.accountId = x.account.id ∧
      x.contact.customerId = x.account.customer.id := by
  exact ⟨x.contact_account_matches, x.contact_customer_matches⟩

/-- Permitted CRM customer messages carry all outreach permission gates. -/
theorem crm_contact_permission_safety
    (message : PermittedCustomerMessage) :
    canSendMarketingMessage message.contact.subscription ∧
      canRetarget message.contact.retargetingConsent ∧
      dataProcessingAllowed message.contact.dataPermission ∧
      message.contact.dataPermission.purpose = ConsentPurpose.Marketing ∧
      message.contact.dataPermission.basis = ProcessingBasis.Consent := by
  exact message.permitted

/-! ### Regulatory and compliance theorems -/

/-- Consent withdrawal propagates to the marketing eligibility gate. -/
theorem regulatory_consent_withdrawal_blocks_marketing
    (state : MarketingConsentState) :
    ¬ marketingAllowed (withdrawMarketingConsent state) := by
  exact consent_withdrawal_blocks_future_marketing state

/-- Consent withdrawal also blocks retargeting and data-processing permission. -/
theorem regulatory_consent_withdrawal_blocks_retargeting_and_processing
    (state : MarketingConsentState) :
    ¬ canRetarget (withdrawMarketingConsent state).retargetingConsent ∧
      ¬ dataProcessingAllowed (withdrawMarketingConsent state).dataPermission := by
  exact ⟨consent_withdrawal_blocks_retargeting state,
    consent_withdrawal_blocks_data_processing state⟩

/-- Purpose limitation prevents reusing a permission for a mismatched purpose. -/
theorem regulatory_purpose_limitation_blocks_mismatched_processing
    (permission : DataProcessingPermission)
    (requested : ConsentPurpose)
    (basis : ProcessingBasis)
    (hMismatch : permission.purpose ≠ requested) :
    ¬ processingAllowedFor permission requested basis := by
  exact purpose_limitation_blocks_mismatched_purpose
    permission requested basis hMismatch

/-- Legal-basis limitation prevents reusing a permission under a mismatched basis. -/
theorem regulatory_basis_limitation_blocks_mismatched_processing
    (permission : DataProcessingPermission)
    (purpose : ConsentPurpose)
    (requestedBasis : ProcessingBasis)
    (hMismatch : permission.basis ≠ requestedBasis) :
    ¬ processingAllowedFor permission purpose requestedBasis := by
  exact processing_basis_limitation_blocks_mismatch
    permission purpose requestedBasis hMismatch

/-- Expired personal data cannot be retained under the same policy and clock. -/
theorem regulatory_expired_data_cannot_be_retained
    (policy : DataRetentionPolicy) (now collectedAt : Timestamp)
    (hExpired : retentionExpired policy now collectedAt) :
    ¬ canRetainPersonalData policy now collectedAt := by
  exact expired_personal_data_cannot_be_retained policy now collectedAt hExpired

/-- Right-to-erasure requests block new personal-data processing. -/
theorem regulatory_erasure_request_blocks_processing
    (permission : DataProcessingPermission)
    (purpose : ConsentPurpose)
    (basis : ProcessingBasis) :
    ¬ canProcessPersonalData ErasureStatus.Requested permission purpose basis := by
  exact erasure_request_blocks_processing permission purpose basis

/-- Completed erasure blocks new personal-data processing. -/
theorem regulatory_completed_erasure_blocks_processing
    (permission : DataProcessingPermission)
    (purpose : ConsentPurpose)
    (basis : ProcessingBasis) :
    ¬ canProcessPersonalData ErasureStatus.Completed permission purpose basis := by
  exact completed_erasure_blocks_processing permission purpose basis

/-- Legal hold blocks right-to-erasure completion. -/
theorem regulatory_legal_hold_blocks_erasure_completion
    (status : ErasureStatus) :
    ¬ canCompleteErasure status true := by
  exact legal_hold_blocks_erasure_completion status

/-- Customer support can view order data but not full payment-token data. -/
theorem support_order_access_excludes_payment_token :
    roleCanAccessData Role.Support AccessPurpose.CustomerSupport DataCategory.OrderData ∧
      ¬ roleCanAccessData Role.Support AccessPurpose.CustomerSupport DataCategory.PaymentToken := by
  exact ⟨support_can_view_order_for_support, support_cannot_view_full_payment_token⟩

/-- Append-only audit logs preserve every pre-existing event. -/
theorem regulatory_append_only_audit_log_preserves_event
    {before after newEvents : List EntityAuditEvent}
    {event : EntityAuditEvent}
    (hAppend : auditLogAppended before after newEvents)
    (hMem : event ∈ before) :
    event ∈ after := by
  exact append_only_audit_log_preserves_event hAppend hMem

/-- Append-only audit logs cannot shrink. -/
theorem regulatory_append_only_audit_log_length_safety
    {before after newEvents : List EntityAuditEvent}
    (hAppend : auditLogAppended before after newEvents) :
    before.length ≤ after.length := by
  exact append_only_audit_log_length_ge hAppend

/-- Audited data access proves both command permission and least-privilege data access. -/
theorem audited_data_access_least_privilege_safety
    (access : AuditedDataAccess) :
    CanPerform access.actor access.action ∧
      roleCanAccessData access.actor access.purpose access.category ∧
      access.event.actor = access.actor ∧
      access.event.action = access.action ∧
      access.event.subjectId = access.subjectId := by
  exact ⟨access.action_allowed, access.data_allowed,
    access.event_actor_matches, access.event_action_matches,
    access.event_subject_matches⟩

/-- Resolved CRM support cases prove status, timing, and SLA safety. -/
theorem crm_support_case_sla_safety
    (case_ : ResolvedSupportCase) :
    case_.case_.status = SupportCaseStatus.Resolved ∧
      case_.case_.openedAt ≤ case_.resolvedAt ∧
      case_.case_.lastUpdatedAt ≤ case_.resolvedAt ∧
      case_.resolvedAt ≤ case_.case_.slaDueAt := by
  exact ⟨case_.status_resolved, case_.opened_le_resolved,
    case_.lastUpdated_le_resolved, case_.resolved_by_sla⟩

/-- CRM retention offers stay inside account value and segment caps. -/
theorem crm_retention_offer_value_safety
    (offer : RetentionOffer) :
    offer.account.status = CRMAccountStatus.Active ∧
    offer.discount ≤ offer.account.lifetimeValue ∧
      offer.discount ≤ offer.segment.maxRetentionDiscount ∧
      offer.segment.minLifetimeValue ≤ offer.account.lifetimeValue ∧
      offer.coupon.minSubtotal ≤ offer.account.lifetimeValue ∧
      offer.usesBefore < offer.coupon.maxUses := by
  exact ⟨retentionOffer_account_active offer,
    retentionOffer_discount_le_lifetimeValue offer,
    retentionOffer_discount_le_segment_cap offer,
    retentionOffer_account_meets_segment_value_floor offer,
    retentionOffer_coupon_minSubtotal_met offer,
    retentionOffer_coupon_usage_below_max offer⟩

/-- Currency-consistent CRM pipelines keep weighted value below gross value. -/
theorem crm_sales_pipeline_safety
    (pipeline : SalesPipeline) :
    opportunitiesUseCurrency pipeline.currency pipeline.opportunities ∧
      opportunityWeightedValueTotal pipeline.opportunities ≤
        opportunityGrossValue pipeline.opportunities := by
  exact ⟨pipeline.currency_consistent,
    salesPipeline_weightedValue_le_grossValue pipeline⟩

/-- Converted CRM leads keep source linkage and opportunity amount bounds. -/
theorem crm_converted_lead_opportunity_safety
    (conversion : ConvertedLeadOpportunity) :
    conversion.lead.status = LeadStatus.Converted ∧
      conversion.opportunity.sourceLead = some conversion.lead.id ∧
      conversion.opportunity.accountId = conversion.lead.accountId ∧
      conversion.opportunity.contactId = conversion.lead.contactId ∧
      conversion.opportunity.currency = conversion.lead.currency ∧
      conversion.opportunity.amount ≤ conversion.lead.estimatedValue := by
  exact ⟨conversion.lead_converted, conversion.opportunity_source_matches,
    conversion.account_matches, conversion.contact_matches, conversion.currency_matches,
    conversion.opportunity_amount_le_estimate⟩

/-- Validated CRM interactions preserve account/contact identity and follow-up ordering. -/
theorem crm_interaction_identity_safety
    (interaction : CRMInteractionForContact) :
    interaction.interaction.accountId = interaction.accountContact.account.id ∧
      interaction.interaction.contactId = interaction.accountContact.contact.id ∧
      interaction.interaction.occurredAt ≤ interaction.interaction.followUpDueAt := by
  exact ⟨interaction.interaction_account_matches,
    interaction.interaction_contact_matches,
    interaction.interaction.followUp_after_occurrence⟩

/-- Validated CRM leads preserve account/contact identity and timestamp ordering. -/
theorem crm_lead_identity_safety
    (lead : LeadForContact) :
    lead.lead.accountId = lead.accountContact.account.id ∧
      lead.lead.contactId = lead.accountContact.contact.id ∧
      lead.lead.createdAt ≤ lead.lead.updatedAt := by
  exact ⟨lead.lead_account_matches, lead.lead_contact_matches,
    lead.lead.created_le_updated⟩

/-- Validated opportunities preserve account/contact identity, stage probability, and timing. -/
theorem crm_opportunity_identity_safety
    (opportunity : OpportunityForContact) :
    opportunity.opportunity.accountId = opportunity.accountContact.account.id ∧
      opportunity.opportunity.contactId = opportunity.accountContact.contact.id ∧
      opportunityStageProbabilityAllowed
        opportunity.opportunity.stage opportunity.opportunity.probability ∧
      opportunity.opportunity.openedAt ≤ opportunity.opportunity.updatedAt ∧
      opportunity.opportunity.openedAt ≤ opportunity.opportunity.expectedCloseAt := by
  exact ⟨opportunity.opportunity_account_matches,
    opportunity.opportunity_contact_matches,
    opportunity.opportunity.probability_matches_stage,
    opportunity.opportunity.opened_le_updated,
    opportunity.opportunity.opened_le_expectedClose⟩

/-- Validated support cases preserve account/contact identity and base timing. -/
theorem crm_support_case_identity_safety
    (case_ : SupportCaseForContact) :
    case_.case_.accountId = case_.accountContact.account.id ∧
      case_.case_.contactId = case_.accountContact.contact.id ∧
      case_.case_.openedAt ≤ case_.case_.lastUpdatedAt ∧
      case_.case_.openedAt ≤ case_.case_.slaDueAt := by
  exact ⟨case_.case_account_matches, case_.case_contact_matches,
    case_.case_.opened_le_lastUpdated, case_.case_.opened_le_slaDue⟩

/-- Logistics shipment plans prove carrier capacity, quote price, and allocation safety. -/
theorem logistics_shipment_plan_safety
    (plan : LogisticsShipmentPlan) :
    orderEligibleForLogistics plan.order ∧
      allocationKeysDistinct plan.fulfillment.allocations ∧
      allocationsMatchCartSkus plan.order.items plan.fulfillment.allocations ∧
      allocationsUseWarehouse plan.warehouse plan.fulfillment.allocations ∧
      plan.quote.service.zone = plan.destination.zone ∧
      cartWeightTotal plan.order.items ≤ plan.package.weight ∧
      plan.package.weight ≤ plan.quote.service.maxWeight ∧
      plan.quote.service.baseCost ≤ plan.quote.price ∧
      plan.fulfillment.requested ≤ allocationsAvailableTotal plan.fulfillment.allocations := by
  exact ⟨plan.order_eligible, plan.fulfillment.allocation_keys_distinct,
    plan.allocations_match_cart_skus, plan.allocations_use_warehouse,
    plan.quote_zone_matches_destination, plan.package_covers_cart_weight,
    shipmentPlan_package_weight_safe plan,
    shipmentPlan_quote_price_covers_base_cost plan,
    shipmentPlan_requested_le_availableTotal plan⟩

/-- Concrete logistics shipments preserve plan identity and timestamp ordering. -/
theorem logistics_shipment_identity_safety
    (shipment : LogisticsShipment) :
    shipment.id = shipment.plan.id ∧ shipment.createdAt ≤ shipment.updatedAt := by
  exact ⟨shipment.id_matches_plan, shipment.created_le_updated⟩

/-- Carrier handoffs preserve quote service identity and timestamp order. -/
theorem logistics_carrier_handoff_safety
    (handoff : CarrierHandoff) :
    handoff.service = handoff.plan.quote.service ∧
      handoff.service.carrierId = handoff.plan.quote.service.carrierId ∧
      handoff.plan.plannedShipAt ≤ handoff.handedOffAt ∧
      handoff.handedOffAt ≤ handoff.acceptanceScanAt := by
  exact ⟨handoff.service_matches_quote, carrierHandoff_carrier_matches_quote handoff,
    handoff.plannedShip_le_handedOff,
    handoff.handedOff_le_acceptanceScan⟩

/-- Tracking histories preserve timestamp order, shipment identity, unique ids, and kind progression. -/
theorem logistics_tracking_history_safety
    (history : TrackingHistory) :
    trackingEventsMonotoneFrom 0 history.events ∧
      trackingEventsForShipment history.shipmentId history.events ∧
      trackingEventsForCarrier history.carrierId history.trackingNumber history.events ∧
      trackingEventIdsDistinct history.events ∧
      trackingEventsProgressFrom TrackingEventKind.LabelCreated history.events := by
  exact ⟨history.events_monotone, history.events_match_shipment,
    history.events_match_carrier, history.event_ids_distinct, history.events_progress⟩

/-- Delivered logistics shipments meet the promised window and include a delivery scan. -/
theorem logistics_delivery_promise_safety
    (shipment : DeliveredShipment) :
    shipment.promise.plan.plannedShipAt ≤ shipment.deliveredAt ∧
      shipment.deliveredAt ≤ shipment.promise.plan.promisedDeliveryAt ∧
      shipment.history.carrierId = shipment.promise.plan.quote.service.carrierId ∧
      shipment.deliveryEvent.kind = TrackingEventKind.DeliveredScan ∧
      shipment.deliveryEvent.carrierId = shipment.history.carrierId ∧
      shipment.deliveryEvent.trackingNumber = shipment.history.trackingNumber ∧
      shipment.deliveryEvent ∈ shipment.history.events := by
  exact ⟨shipment.shipped_le_delivered,
    deliveredShipment_deliveredAt_le_plan_promised shipment,
    shipment.history_carrier_matches_quote,
    shipment.delivery_event_kind, shipment.delivery_event_carrier,
    shipment.delivery_event_trackingNumber, shipment.delivery_event_in_history⟩

/-- Warehouse transfers stay inside source availability and in-transit quantities. -/
theorem logistics_transfer_stock_safety
    (transfer : WarehouseTransfer) :
    transfer.requested ≤ availableStock transfer.sourceStock ∧
      transfer.received ≤ transfer.inTransit ∧
      transfer.received ≤ transfer.requested ∧
      transfer.fromWarehouse.id ≠ transfer.toWarehouse.id := by
  exact ⟨transfer.requested_le_available, transfer.received_le_inTransit,
    warehouseTransfer_received_le_requested transfer,
    transfer.warehouses_distinct⟩

/-- Return authorizations stay inside order quantity and refundable ledger amount. -/
theorem logistics_return_authorization_safety
    (authorization : ReturnAuthorization) :
    returnLinesMatchOrderSkus authorization.order.items authorization.lines ∧
      returnLinesQuantityTotal authorization.lines = authorization.quantity ∧
      returnLinesRefundTotal authorization.lines = authorization.refundAmount ∧
      authorization.quantity ≤ cartQuantityTotal authorization.order.items ∧
      authorization.refundAmount ≤ remainingRefundAmount authorization.ledger ∧
      authorization.refundAmount ≤ authorization.order.total := by
  exact ⟨authorization.lines_match_order_skus, authorization.quantity_correct,
    authorization.refund_correct, authorization.quantity_le_order_quantity,
    returnAuthorization_refund_le_remaining authorization,
    returnAuthorization_refund_le_order_total authorization⟩

/-- Return receipts require approval and stay within quantity, refund, and timing bounds. -/
theorem logistics_return_receipt_safety
    (receipt : ReturnReceipt) :
    receipt.authorization.status = ReturnAuthorizationStatus.Approved ∧
      receipt.receivedQuantity ≤ cartQuantityTotal receipt.authorization.order.items ∧
      receipt.refundIssued ≤ remainingRefundAmount receipt.authorization.ledger ∧
      receipt.refundIssued ≤ receipt.authorization.order.total ∧
      receipt.authorization.decidedAt ≤ receipt.receivedAt := by
  exact ⟨receipt.authorization_approved,
    returnReceipt_received_le_order_quantity receipt,
    returnReceipt_refund_le_remaining receipt,
    returnReceipt_refund_le_order_total receipt,
    receipt.decided_le_received⟩

/-- Shipments tied to CRM orders preserve order identity and shipment capacity safety. -/
theorem shipment_for_crm_order_safety
    (shipment : ShipmentForCRMOrder) :
    shipment.crmOrder.account.status = CRMAccountStatus.Active ∧
      shipment.plan.order.id = shipment.crmOrder.order.id ∧
      shipment.plan.package.weight ≤ shipment.plan.quote.service.maxWeight := by
  exact ⟨crmOrderContact_account_active shipment.crmOrder,
    shipmentForCRMOrder_order_id_matches shipment,
    shipmentForCRMOrder_package_weight_safe shipment⟩

/-- Logistics exceptions escalated to CRM support preserve shipment and order linkage. -/
theorem logistics_exception_escalation_safety
    (escalation : LogisticsExceptionSupportCase) :
    escalation.exception.shipmentId = escalation.shipment.id ∧
      escalation.supportCase.orderId = some escalation.shipment.order.id ∧
      escalation.supportCase.status = SupportCaseStatus.Escalated ∧
      escalation.exception.raisedAt ≤ escalation.supportCase.openedAt := by
  exact ⟨escalation.exception_shipment_matches,
    escalation.support_case_order_matches,
    escalation.support_case_escalated,
    escalation.exception_raised_before_case_opened⟩

/-- CRM-approved return handling stays within both refund and received-quantity bounds. -/
theorem crm_approved_return_handling_safety
    (handling : CRMApprovedReturnHandling) :
    handling.authorization.status = ReturnAuthorizationStatus.Approved ∧
      handling.receipt.refundIssued ≤ remainingRefundAmount handling.authorization.ledger ∧
      handling.receipt.refundIssued ≤ handling.authorization.order.total ∧
      handling.receipt.receivedQuantity ≤
        cartQuantityTotal handling.authorization.order.items := by
  exact ⟨handling.approved, crmApprovedReturnHandling_refund_le_remaining handling,
    crmApprovedReturnHandling_refund_le_order_total handling,
    crmApprovedReturnHandling_received_le_order_quantity handling⟩


end CommerceTheory
