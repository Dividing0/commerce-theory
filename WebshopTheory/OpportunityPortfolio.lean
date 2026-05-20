import WebshopTheory.Forecasting

namespace WebShopTheoryComplete

/-! ## 18. Abstract dropship opportunity portfolio selection -/

/-!
The opportunity portfolio abstracts a selection problem: choose dropship
candidates while staying within capital and minimum-profit constraints. It is
small by design so later optimization code can target these same invariants.
-/

/-- Data shape for `DistributorProduct`; proof fields record invariants when needed. -/
structure DistributorProduct where
  distributorId : SupplierId
  sku : Sku
  unitCost : Money
  supplierShippingPerUnit : Money
  availableQty : Quantity
  minOrderQty : Quantity
  currency : Currency
  active : Bool

/-- Data shape for `DropshipOpportunityCandidate`; proof fields record invariants when needed. -/
structure DropshipOpportunityCandidate where
  sku : Sku
  units : Quantity
  targetPrice : Money
  requiredCapital : Money
  expectedProfit : Money
  minProfit : Money
  competitorPrice : Money
  costs : DropshipProfitCosts
  capital_pos : 0 < requiredCapital
  expectedProfit_ge_minProfit : minProfit ≤ expectedProfit
  price_profitable : priceProfitableForMinProfit targetPrice 0 costs minProfit
  targetPrice_le_competitor : targetPrice ≤ competitorPrice

/-- Computes or checks `candidatesCapitalTotal` using the validated data in this module. -/
def candidatesCapitalTotal : List DropshipOpportunityCandidate → Money
  | [] => 0
  | c :: rest => c.requiredCapital + candidatesCapitalTotal rest

/-- Computes or checks `candidatesProfitTotal` using the validated data in this module. -/
def candidatesProfitTotal : List DropshipOpportunityCandidate → Money
  | [] => 0
  | c :: rest => c.expectedProfit + candidatesProfitTotal rest

/-- Computes or checks `candidatesMinProfitTotal` using the validated data in this module. -/
def candidatesMinProfitTotal : List DropshipOpportunityCandidate → Money
  | [] => 0
  | c :: rest => c.minProfit + candidatesMinProfitTotal rest

/-- Data shape for `DropshipOpportunityPortfolio`; proof fields record invariants when needed. -/
structure DropshipOpportunityPortfolio where
  selected : List DropshipOpportunityCandidate
  investmentFund : Money
  capital_le_fund : candidatesCapitalTotal selected ≤ investmentFund

/-- States the safety property captured by `opportunityPortfolio_capital_safe`. -/
theorem opportunityPortfolio_capital_safe (p : DropshipOpportunityPortfolio) :
    candidatesCapitalTotal p.selected ≤ p.investmentFund := by
  exact p.capital_le_fund

/-- States the safety property captured by `candidate_profit_safe`. -/
theorem candidate_profit_safe (c : DropshipOpportunityCandidate) :
    c.minProfit ≤ c.expectedProfit := by
  exact c.expectedProfit_ge_minProfit


end WebShopTheoryComplete
