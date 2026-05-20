import CommerceTheory.DropshipProfit

namespace CommerceTheory

/-! ## 11. Competitor pricing, price floors, repricing, and opportunity safety -/

/-!
Competitor pricing combines market observations with profit floors. The module
shows when matching or undercutting a competitor is safe, and when it is
impossible without violating the minimum-profit requirement.
-/

/-- Data shape for `CompetitorOffer`; proof fields record invariants when needed. -/
structure CompetitorOffer where
  competitorId : CompetitorId
  sku : Sku
  price : Money
  currency : Currency
  active : Bool
  inStock : Bool
  observedAt : Timestamp

/-- Computes or checks `competitorOfferRelevant` using the validated data in this module. -/
def competitorOfferRelevant (offer : CompetitorOffer) (sku : Sku) (currency : Currency) : Prop :=
  offer.sku = sku ∧ offer.currency = currency ∧ offer.active = true ∧ offer.inStock = true

/-- Computes or checks `priceSnapshotFresh` using the validated data in this module. -/
def priceSnapshotFresh (now maxAge observedAt : Timestamp) : Prop :=
  observedAt ≤ now ∧ now - observedAt ≤ maxAge

/-- Closed set of cases for `TrustLevel` in the commerce domain model. -/
inductive TrustLevel where
  | Low
  | Medium
  | High
deriving DecidableEq, Repr

/-- Computes or checks `trustAllowsAutoRepricing` using the validated data in this module. -/
def trustAllowsAutoRepricing : TrustLevel → Prop
  | TrustLevel.Low => False
  | TrustLevel.Medium => True
  | TrustLevel.High => True

/-- States the safety property captured by `lowTrust_not_autoRepricing`. -/
theorem lowTrust_not_autoRepricing :
    ¬ trustAllowsAutoRepricing TrustLevel.Low := by
  simp [trustAllowsAutoRepricing]

/-- Data shape for `CompetitorPriceBenchmark`; proof fields record invariants when needed. -/
structure CompetitorPriceBenchmark where
  sku : Sku
  currency : Currency
  offers : List CompetitorOffer
  bestOffer : CompetitorOffer
  bestOffer_in_offers : bestOffer ∈ offers
  bestOffer_relevant : competitorOfferRelevant bestOffer sku currency
  bestOffer_is_lowest :
    ∀ other : CompetitorOffer,
      other ∈ offers → competitorOfferRelevant other sku currency → bestOffer.price ≤ other.price

/-- States the safety property captured by `benchmark_bestPrice_le_other_relevant_price`. -/
theorem benchmark_bestPrice_le_other_relevant_price
    (b : CompetitorPriceBenchmark) (other : CompetitorOffer)
    (hmem : other ∈ b.offers) (hrel : competitorOfferRelevant other b.sku b.currency) :
    b.bestOffer.price ≤ other.price := by
  exact b.bestOffer_is_lowest other hmem hrel

/-- Computes or checks `customerNetAtOfferPrice` using the validated data in this module. -/
def customerNetAtOfferPrice (price discount : Money) : Money :=
  price - discount

/-- Computes or checks `profitAtOfferPrice` using the validated data in this module. -/
def profitAtOfferPrice (price discount : Money) (costs : DropshipProfitCosts) : Money :=
  profitAmount (customerNetAtOfferPrice price discount) (dropshipProfitCostsTotal costs)

/-- Computes or checks `profitablePriceFloor` using the validated data in this module. -/
def profitablePriceFloor (costs : DropshipProfitCosts) (minProfit discount : Money) : Money :=
  dropshipProfitCostsTotal costs + minProfit + discount

/-- Computes or checks `priceProfitableForMinProfit` using the validated data in this module. -/
def priceProfitableForMinProfit
    (price discount : Money) (costs : DropshipProfitCosts) (minProfit : Money) : Prop :=
  profitablePriceFloor costs minProfit discount ≤ price

/-- States the safety property captured by `profitablePrice_guarantees_minProfit`. -/
theorem profitablePrice_guarantees_minProfit
    (price discount : Money) (costs : DropshipProfitCosts) (minProfit : Money)
    (h : priceProfitableForMinProfit price discount costs minProfit) :
    minProfit ≤ profitAtOfferPrice price discount costs := by
  unfold priceProfitableForMinProfit at h
  unfold profitablePriceFloor at h
  unfold profitAtOfferPrice
  unfold customerNetAtOfferPrice
  exact profitAmount_ge_minProfit
    (price - discount)
    (dropshipProfitCostsTotal costs)
    minProfit
    (Nat.le_sub_of_add_le h)

/-- Computes or checks `priceAtOrBelowCompetitor` using the validated data in this module. -/
def priceAtOrBelowCompetitor (ownPrice competitorPrice : Money) : Prop :=
  ownPrice ≤ competitorPrice

/-- States the safety property captured by `impossible_to_match_competitor_below_floor`. -/
theorem impossible_to_match_competitor_below_floor
    (costs : DropshipProfitCosts) (minProfit discount competitorPrice ownPrice : Money)
    (hbelow : competitorPrice < profitablePriceFloor costs minProfit discount)
    (hprofit : priceProfitableForMinProfit ownPrice discount costs minProfit)
    (hcompetitive : priceAtOrBelowCompetitor ownPrice competitorPrice) :
    False := by
  unfold priceProfitableForMinProfit at hprofit
  unfold priceAtOrBelowCompetitor at hcompetitive
  exact (not_lt_of_ge (hprofit.trans hcompetitive)) hbelow

/-- Computes or checks `undercutPrice` using the validated data in this module. -/
def undercutPrice (competitorPrice delta : Money) : Money :=
  competitorPrice - delta

/-- States the safety property captured by `undercutPrice_le_competitorPrice`. -/
theorem undercutPrice_le_competitorPrice (competitorPrice delta : Money) :
    undercutPrice competitorPrice delta ≤ competitorPrice := by
  unfold undercutPrice
  exact Nat.sub_le competitorPrice delta

/-- Closed set of cases for `CompetitivePricingStrategy` in the commerce domain model. -/
inductive CompetitivePricingStrategy where
  | Match
  | Undercut : Money → CompetitivePricingStrategy
  | Premium : Money → CompetitivePricingStrategy
deriving DecidableEq, Repr

/-- Computes or checks `targetPriceFromStrategy` using the validated data in this module. -/
def targetPriceFromStrategy (strategy : CompetitivePricingStrategy) (referencePrice : Money) : Money :=
  match strategy with
  | CompetitivePricingStrategy.Match => referencePrice
  | CompetitivePricingStrategy.Undercut delta => referencePrice - delta
  | CompetitivePricingStrategy.Premium premium => referencePrice + premium

/-- States the safety property captured by `undercutStrategy_target_le_reference`. -/
theorem undercutStrategy_target_le_reference (referencePrice delta : Money) :
    targetPriceFromStrategy (CompetitivePricingStrategy.Undercut delta) referencePrice ≤ referencePrice := by
  simp [targetPriceFromStrategy]

/-- Data shape for `CompetitorAwareDropshipOffer`; proof fields record invariants when needed. -/
structure CompetitorAwareDropshipOffer where
  offer : DropshipOffer
  benchmark : CompetitorPriceBenchmark
  discount : Money
  costs : DropshipProfitCosts
  minProfit : Money
  same_sku : benchmark.sku = offer.sku
  same_currency : benchmark.currency = offer.currency
  salePrice_profitable : priceProfitableForMinProfit offer.saleUnitPrice discount costs minProfit
  salePrice_le_bestCompetitor : offer.saleUnitPrice ≤ benchmark.bestOffer.price

/-- States the safety property captured by `competitorAwareDropshipOffer_profit_guaranteed`. -/
theorem competitorAwareDropshipOffer_profit_guaranteed
    (x : CompetitorAwareDropshipOffer) :
    x.minProfit ≤ profitAtOfferPrice x.offer.saleUnitPrice x.discount x.costs := by
  exact profitablePrice_guarantees_minProfit
    x.offer.saleUnitPrice x.discount x.costs x.minProfit x.salePrice_profitable

/-- States the safety property captured by `competitorAwareDropshipOffer_price_le_every_relevant_competitor`. -/
theorem competitorAwareDropshipOffer_price_le_every_relevant_competitor
    (x : CompetitorAwareDropshipOffer) (other : CompetitorOffer)
    (hmem : other ∈ x.benchmark.offers)
    (hrel : competitorOfferRelevant other x.benchmark.sku x.benchmark.currency) :
    x.offer.saleUnitPrice ≤ other.price := by
  have hbest := x.benchmark.bestOffer_is_lowest other hmem hrel
  have hown := x.salePrice_le_bestCompetitor
  exact hown.trans hbest


end CommerceTheory
