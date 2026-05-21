import CommerceTheory.EventLanguage
import CommerceTheory.EventReplay
import CommerceTheory.ImplicitInvariants
import CommerceTheory.InventoryAlgorithms
import CommerceTheory.KeyedTotals
import CommerceTheory.OpportunityRanking
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

/-- Safe marketplace feed lines publish prices inside their channel price policy. -/
theorem marketplace_feed_price_policy_safety (f : SafeProductFeedLine) :
    f.pricePolicy.minPrice ≤ f.price ∧ f.price ≤ f.pricePolicy.maxPrice := by
  exact f.price_valid

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
      benchmark.now - benchmark.benchmark.bestOffer.observedAt ≤ benchmark.maxAge ∧
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
      conversion.now - conversion.rate.observedAt ≤ conversion.maxAge := by
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

/-- CSLib reachability for the normal dropship supplier purchase-order workflow. -/
theorem dropship_po_workflow_reaches_delivered :
    dropshipPOLTS.CanReach DropshipPOStatus.Created DropshipPOStatus.Delivered := by
  exact dropshipPO_can_reach_delivered

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
