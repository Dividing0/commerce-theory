import WebshopTheory.CompetitorPricing

namespace WebShopTheoryComplete

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

/-- Closed set of cases for `PromotionStackingPolicy` in the webshop domain model. -/
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

/-- States the safety property captured by `promotionSet_respects_profit_floor`. -/
theorem promotionSet_respects_profit_floor (p : AcceptedPromotionSet) :
    p.profitFloor ≤ p.resultingPrice := by
  exact p.floor_le_price

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


end WebShopTheoryComplete
