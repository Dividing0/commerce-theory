import CommerceTheory.CompetitorPricing

namespace CommerceTheory

/-! ## 12. Promotions, bundles, MAP/MSRP, search, and recommendations -/

/-!
Merchandising covers brand pricing policy, bundle component reservations,
promotion stacking, and search result safety. The proofs focus on preserving MAP
rules, stock availability, and profit floors.
-/

/-- Data shape for `BrandPricingPolicy`; proof fields record invariants when needed. -/
structure BrandPricingPolicy where
  mapPrice : Money
  msrp : Money
  map_le_msrp : mapPrice ≤ msrp

/-- Computes or checks `advertisedPriceAllowed` using the validated data in this module. -/
def advertisedPriceAllowed (policy : BrandPricingPolicy) (advertisedPrice : Money) : Prop :=
  policy.mapPrice ≤ advertisedPrice

/-- States the safety property captured by `advertisedPriceAllowed_ge_map`. -/
theorem advertisedPriceAllowed_ge_map
    (policy : BrandPricingPolicy) (advertisedPrice : Money)
    (h : advertisedPriceAllowed policy advertisedPrice) :
    policy.mapPrice ≤ advertisedPrice := by
  exact h

/-- Brand MAP cannot exceed MSRP. -/
theorem brandPricingPolicy_map_le_msrp (policy : BrandPricingPolicy) :
    policy.mapPrice ≤ policy.msrp := by
  exact policy.map_le_msrp

/-- Advertising exactly at MSRP is always MAP-compliant. -/
theorem msrp_advertisedPriceAllowed (policy : BrandPricingPolicy) :
    advertisedPriceAllowed policy policy.msrp := by
  exact policy.map_le_msrp

/-- Data shape for `BundleComponent`; proof fields record invariants when needed. -/
structure BundleComponent where
  sku : Sku
  unitsPerBundle : Quantity
  stockAvailable : Quantity
  units_pos : 0 < unitsPerBundle

/-- Computes or checks `componentRequiredForBundles` using the validated data in this module. -/
def componentRequiredForBundles (bundleQty : Quantity) (component : BundleComponent) : Quantity :=
  bundleQty * component.unitsPerBundle

/-- Computes or checks `componentCanFulfillBundles` using the validated data in this module. -/
def componentCanFulfillBundles (bundleQty : Quantity) (component : BundleComponent) : Prop :=
  componentRequiredForBundles bundleQty component ≤ component.stockAvailable

/-- Data shape for `BundleReservation`; proof fields record invariants when needed. -/
structure BundleReservation where
  bundleQty : Quantity
  components : List BundleComponent
  all_components_safe : ∀ c ∈ components, componentCanFulfillBundles bundleQty c

/-- States the safety property captured by `bundleReservation_component_safe`. -/
theorem bundleReservation_component_safe
    (r : BundleReservation) (c : BundleComponent) (hmem : c ∈ r.components) :
    componentRequiredForBundles r.bundleQty c ≤ c.stockAvailable := by
  exact r.all_components_safe c hmem

/-- Closed set of cases for `PromotionStackingPolicy` in the commerce domain model. -/
inductive PromotionStackingPolicy where
  | Exclusive
  | Stackable
  | StackableWithCap
deriving DecidableEq, Repr

/-- Data shape for `AcceptedPromotionSet`; proof fields record invariants when needed. -/
structure AcceptedPromotionSet where
  resultingPrice : Money
  totalDiscount : Money
  discountCap : Money
  profitFloor : Money
  discount_le_cap : totalDiscount ≤ discountCap
  floor_le_price : profitFloor ≤ resultingPrice

/-- Interprets promotion-stacking policies for a concrete accepted promotion set. -/
def promotionSetAllowedByPolicy
    (policy : PromotionStackingPolicy) (promotionCount : Nat)
    (p : AcceptedPromotionSet) : Prop :=
  match policy with
  | PromotionStackingPolicy.Exclusive => promotionCount ≤ 1
  | PromotionStackingPolicy.Stackable => True
  | PromotionStackingPolicy.StackableWithCap => p.totalDiscount ≤ p.discountCap

/-- States the safety property captured by `promotionSet_respects_profit_floor`. -/
theorem promotionSet_respects_profit_floor (p : AcceptedPromotionSet) :
    p.profitFloor ≤ p.resultingPrice := by
  exact p.floor_le_price

/-- Accepted promotion sets respect their configured discount cap. -/
theorem promotionSet_respects_discount_cap (p : AcceptedPromotionSet) :
    p.totalDiscount ≤ p.discountCap := by
  exact p.discount_le_cap

/-- Accepted promotion sets are allowed under the capped-stacking policy. -/
theorem promotionSet_allowed_with_cap_policy
    (promotionCount : Nat) (p : AcceptedPromotionSet) :
    promotionSetAllowedByPolicy
      PromotionStackingPolicy.StackableWithCap promotionCount p := by
  exact p.discount_le_cap

/-- Exclusive stacking policy means at most one accepted promotion. -/
theorem exclusivePromotionPolicy_at_most_one
    (promotionCount : Nat) (p : AcceptedPromotionSet)
    (h : promotionSetAllowedByPolicy
      PromotionStackingPolicy.Exclusive promotionCount p) :
    promotionCount ≤ 1 := by
  exact h

/-- Data shape for `SearchResultItem`; proof fields record invariants when needed. -/
structure SearchResultItem where
  sku : Sku
  archived : Bool
  inStock : Bool
  marginSafe : Bool

/-- Data shape for `ValidSearchResultItem`; proof fields record invariants when needed. -/
structure ValidSearchResultItem where
  item : SearchResultItem
  not_archived : item.archived = false
  sellable : item.inStock = true
  margin_safe : item.marginSafe = true

/-- States the safety property captured by `validSearchResult_sellable`. -/
theorem validSearchResult_sellable (x : ValidSearchResultItem) :
    x.item.inStock = true := by
  exact x.sellable

/-- Valid search results exclude archived items. -/
theorem validSearchResult_not_archived (x : ValidSearchResultItem) :
    x.item.archived = false := by
  exact x.not_archived

/-- Valid search results keep only margin-safe items. -/
theorem validSearchResult_margin_safe (x : ValidSearchResultItem) :
    x.item.marginSafe = true := by
  exact x.margin_safe

/-- Compact reusable form of all search-result safety checks. -/
theorem validSearchResult_safe (x : ValidSearchResultItem) :
    x.item.archived = false ∧ x.item.inStock = true ∧ x.item.marginSafe = true := by
  exact ⟨x.not_archived, x.sellable, x.margin_safe⟩


end CommerceTheory
