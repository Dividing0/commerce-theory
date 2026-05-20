import WebshopTheory.Dropshipping

namespace WebShopTheoryComplete

/-! ## 10. Dropship profit engine and guaranteed earnings -/

/-!
This module collects dropship cost components and proves profit guarantees. It
uses conservative upper bounds so a quote can remain safe even when actual costs
are only known to be below a maximum.
-/

/-- Data shape for `DropshipProfitCosts`; proof fields record invariants when needed. -/
structure DropshipProfitCosts where
  supplierGoods : Money
  supplierShipping : Money
  marketplaceFee : Money
  paymentFee : Money
  adSpend : Money
  returnReserve : Money
  tax : Money
  otherCosts : Money

/-- Computes or checks `dropshipProfitCostsTotal` using the validated data in this module. -/
def dropshipProfitCostsTotal (c : DropshipProfitCosts) : Money :=
  c.supplierGoods + c.supplierShipping + c.marketplaceFee + c.paymentFee +
  c.adSpend + c.returnReserve + c.tax + c.otherCosts

/-- States the safety property captured by `supplierGoods_le_dropshipCostsTotal`. -/
theorem supplierGoods_le_dropshipCostsTotal (c : DropshipProfitCosts) :
    c.supplierGoods ≤ dropshipProfitCostsTotal c := by
  unfold dropshipProfitCostsTotal
  calc
    c.supplierGoods ≤ c.supplierGoods + c.supplierShipping :=
      Nat.le_add_right c.supplierGoods c.supplierShipping
    _ ≤ c.supplierGoods + c.supplierShipping + c.marketplaceFee :=
      Nat.le_add_right (c.supplierGoods + c.supplierShipping) c.marketplaceFee
    _ ≤ c.supplierGoods + c.supplierShipping + c.marketplaceFee + c.paymentFee :=
      Nat.le_add_right (c.supplierGoods + c.supplierShipping + c.marketplaceFee) c.paymentFee
    _ ≤ c.supplierGoods + c.supplierShipping + c.marketplaceFee + c.paymentFee + c.adSpend :=
      Nat.le_add_right
        (c.supplierGoods + c.supplierShipping + c.marketplaceFee + c.paymentFee) c.adSpend
    _ ≤ c.supplierGoods + c.supplierShipping + c.marketplaceFee + c.paymentFee +
          c.adSpend + c.returnReserve :=
      Nat.le_add_right
        (c.supplierGoods + c.supplierShipping + c.marketplaceFee + c.paymentFee + c.adSpend)
        c.returnReserve
    _ ≤ c.supplierGoods + c.supplierShipping + c.marketplaceFee + c.paymentFee +
          c.adSpend + c.returnReserve + c.tax :=
      Nat.le_add_right
        (c.supplierGoods + c.supplierShipping + c.marketplaceFee + c.paymentFee +
          c.adSpend + c.returnReserve)
        c.tax
    _ ≤ c.supplierGoods + c.supplierShipping + c.marketplaceFee + c.paymentFee +
          c.adSpend + c.returnReserve + c.tax + c.otherCosts :=
      Nat.le_add_right
        (c.supplierGoods + c.supplierShipping + c.marketplaceFee + c.paymentFee +
          c.adSpend + c.returnReserve + c.tax)
        c.otherCosts

/-- Computes or checks `revenueAfterDiscount` using the validated data in this module. -/
def revenueAfterDiscount (gross discount : Money) : Money :=
  gross - discount

/-- Computes or checks `requiredRevenueForProfit` using the validated data in this module. -/
def requiredRevenueForProfit (totalCosts minProfit : Money) : Money :=
  totalCosts + minProfit

/-- Computes or checks `requiredGrossForProfit` using the validated data in this module. -/
def requiredGrossForProfit (totalCosts minProfit discount : Money) : Money :=
  totalCosts + minProfit + discount

/-- Data shape for `GuaranteedDropshipProfitQuote`; proof fields record invariants when needed. -/
structure GuaranteedDropshipProfitQuote where
  revenue : Money
  costs : DropshipProfitCosts
  minProfit : Money
  profit : Money
  profit_correct : profit = profitAmount revenue (dropshipProfitCostsTotal costs)
  costs_plus_minProfit_le_revenue : dropshipProfitCostsTotal costs + minProfit ≤ revenue

/-- States the safety property captured by `guaranteedQuote_profit_ge_minProfit`. -/
theorem guaranteedQuote_profit_ge_minProfit (q : GuaranteedDropshipProfitQuote) :
    q.minProfit ≤ q.profit := by
  rw [q.profit_correct]
  exact profitAmount_ge_minProfit q.revenue (dropshipProfitCostsTotal q.costs)
    q.minProfit q.costs_plus_minProfit_le_revenue

/-- Data shape for `DropshipCostUpperBounds`; proof fields record invariants when needed. -/
structure DropshipCostUpperBounds where
  actual : DropshipProfitCosts
  upper : DropshipProfitCosts
  supplierGoods_le : actual.supplierGoods ≤ upper.supplierGoods
  supplierShipping_le : actual.supplierShipping ≤ upper.supplierShipping
  marketplaceFee_le : actual.marketplaceFee ≤ upper.marketplaceFee
  paymentFee_le : actual.paymentFee ≤ upper.paymentFee
  adSpend_le : actual.adSpend ≤ upper.adSpend
  returnReserve_le : actual.returnReserve ≤ upper.returnReserve
  tax_le : actual.tax ≤ upper.tax
  otherCosts_le : actual.otherCosts ≤ upper.otherCosts

/-- States the safety property captured by `actualCostsTotal_le_upperCostsTotal`. -/
theorem actualCostsTotal_le_upperCostsTotal (b : DropshipCostUpperBounds) :
    dropshipProfitCostsTotal b.actual ≤ dropshipProfitCostsTotal b.upper := by
  unfold dropshipProfitCostsTotal
  exact
    Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add b.supplierGoods_le b.supplierShipping_le)
                b.marketplaceFee_le)
              b.paymentFee_le)
            b.adSpend_le)
          b.returnReserve_le)
        b.tax_le)
      b.otherCosts_le

/-- States the safety property captured by `profit_guaranteed_from_upper_cost_bound`. -/
theorem profit_guaranteed_from_upper_cost_bound
    (revenue minProfit : Money) (b : DropshipCostUpperBounds)
    (h : dropshipProfitCostsTotal b.upper + minProfit ≤ revenue) :
    minProfit ≤ profitAmount revenue (dropshipProfitCostsTotal b.actual) := by
  have hactual_le_upper := actualCostsTotal_le_upperCostsTotal b
  have hactual : dropshipProfitCostsTotal b.actual + minProfit ≤ revenue := by
    exact (Nat.add_le_add_right hactual_le_upper minProfit).trans h
  exact profitAmount_ge_minProfit revenue (dropshipProfitCostsTotal b.actual) minProfit hactual

/-- Computes or checks `adSpendSafeForMinProfit` using the validated data in this module. -/
def adSpendSafeForMinProfit
    (revenue nonAdCosts adSpend minProfit : Money) : Prop :=
  nonAdCosts + adSpend + minProfit ≤ revenue

/-- Computes or checks `profitAfterAdSpend` using the validated data in this module. -/
def profitAfterAdSpend (revenue nonAdCosts adSpend : Money) : Money :=
  profitAmount revenue (nonAdCosts + adSpend)

/-- States the safety property captured by `safeAdSpend_guarantees_minProfit`. -/
theorem safeAdSpend_guarantees_minProfit
    (revenue nonAdCosts adSpend minProfit : Money)
    (h : adSpendSafeForMinProfit revenue nonAdCosts adSpend minProfit) :
    minProfit ≤ profitAfterAdSpend revenue nonAdCosts adSpend := by
  unfold adSpendSafeForMinProfit at h
  unfold profitAfterAdSpend
  exact profitAmount_ge_minProfit revenue (nonAdCosts + adSpend) minProfit h

/-- Computes or checks `profitLossInt` using the validated data in this module. -/
def profitLossInt (revenue totalCosts : Money) : Int :=
  Int.ofNat revenue - Int.ofNat totalCosts

/-- States the safety property captured by `profitLossInt_nonnegative_if_costs_le_revenue`. -/
theorem profitLossInt_nonnegative_if_costs_le_revenue
    (revenue totalCosts : Money) (h : totalCosts ≤ revenue) :
    0 ≤ profitLossInt revenue totalCosts := by
  unfold profitLossInt
  exact sub_nonneg.mpr (Int.ofNat_le.mpr h)


end WebShopTheoryComplete
