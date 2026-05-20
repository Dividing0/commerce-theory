import CommerceTheory.Forecasting

namespace CommerceTheory

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

/-- Across a candidate list, expected profit covers the sum of minimum profits. -/
theorem candidatesMinProfitTotal_le_profitTotal
    (candidates : List DropshipOpportunityCandidate) :
    candidatesMinProfitTotal candidates ≤ candidatesProfitTotal candidates := by
  induction candidates with
  | nil =>
      simp [candidatesMinProfitTotal, candidatesProfitTotal]
  | cons c rest ih =>
      simpa [candidatesMinProfitTotal, candidatesProfitTotal] using
        Nat.add_le_add c.expectedProfit_ge_minProfit ih

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

/-- Candidate target price is profit-safe under its modeled cost floor. -/
theorem candidate_targetPrice_profit_safe (c : DropshipOpportunityCandidate) :
    c.minProfit ≤ profitAtOfferPrice c.targetPrice 0 c.costs := by
  exact profitablePrice_guarantees_minProfit c.targetPrice 0 c.costs c.minProfit c.price_profitable

/-- Candidate target price is no higher than its competitor reference price. -/
theorem candidate_targetPrice_competitive (c : DropshipOpportunityCandidate) :
    c.targetPrice ≤ c.competitorPrice := by
  exact c.targetPrice_le_competitor

/-- A validated portfolio's expected-profit total covers selected minimum profits. -/
theorem opportunityPortfolio_expectedProfit_covers_minProfit
    (p : DropshipOpportunityPortfolio) :
    candidatesMinProfitTotal p.selected ≤ candidatesProfitTotal p.selected := by
  exact candidatesMinProfitTotal_le_profitTotal p.selected


end CommerceTheory
