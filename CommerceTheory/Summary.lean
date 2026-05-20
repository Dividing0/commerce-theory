import CommerceTheory.OpportunityPortfolio

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


end CommerceTheory
