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


end CommerceTheory
