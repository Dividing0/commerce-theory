import CommerceTheory.EventLanguage
import CommerceTheory.EventReplay
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

/-- The coarse order-event validator accepts a regular language. -/
theorem order_event_validator_language_regular :
    (Cslib.Automata.Acceptor.language orderEventValidator).IsRegular := by
  exact orderEventValidator_language_regular

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


end CommerceTheory
