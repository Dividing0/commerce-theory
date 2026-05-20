import WebshopTheory.Foundation

namespace WebShopTheoryComplete

/-! ## 1. Catalog, content, and product data quality -/

/-!
Catalog objects are deliberately small. The important pattern is that structures
such as `ProductCatalogEntry` and `ValidListingContent` include proof fields.
Those fields mean a value of the structure is already validated, and later code
can reuse the validation without rechecking it.
-/

/-- Closed set of cases for `ProductStatus` in the webshop domain model. -/
inductive ProductStatus where
  | Draft
  | Active
  | Archived
  | Discontinued
deriving DecidableEq, Repr

/-- Data shape for `Brand`; proof fields record invariants when needed. -/
structure Brand where
  id : Id
  name : String

/-- Data shape for `Category`; proof fields record invariants when needed. -/
structure Category where
  id : Id
  name : String

/-- Data shape for `Product`; proof fields record invariants when needed. -/
structure Product where
  id : ProductId
  brand : Brand
  category : Category
  status : ProductStatus

/-- Data shape for `ProductVariant`; proof fields record invariants when needed. -/
structure ProductVariant where
  id : VariantId
  productId : ProductId
  sku : Sku
  active : Bool

/-- A product paired with one of its variants, plus proof that the pair matches. -/
structure ProductCatalogEntry where
  product : Product
  variant : ProductVariant
  variant_belongs_to_product : variant.productId = product.id

/-- States the safety property captured by `catalogEntry_variant_belongs_to_product`. -/
theorem catalogEntry_variant_belongs_to_product (e : ProductCatalogEntry) :
    e.variant.productId = e.product.id := by
  exact e.variant_belongs_to_product

/-- Data shape for `ImageAsset`; proof fields record invariants when needed. -/
structure ImageAsset where
  id : Id
  width : Nat
  height : Nat

/-- Data shape for `ListingContent`; proof fields record invariants when needed. -/
structure ListingContent where
  titleLength : Nat
  imageCount : Nat
  requiredAttributesFilled : Bool

/-- Data shape for `MarketplaceContentPolicy`; proof fields record invariants when needed. -/
structure MarketplaceContentPolicy where
  maxTitleLength : Nat
  minImageCount : Nat

/-- Listing content that has already passed marketplace policy checks. -/
structure ValidListingContent where
  content : ListingContent
  policy : MarketplaceContentPolicy
  title_ok : content.titleLength ≤ policy.maxTitleLength
  images_ok : policy.minImageCount ≤ content.imageCount
  attrs_ok : content.requiredAttributesFilled = true

/-- States the safety property captured by `validListingContent_title_ok`. -/
theorem validListingContent_title_ok (x : ValidListingContent) :
    x.content.titleLength ≤ x.policy.maxTitleLength := by
  exact x.title_ok


end WebShopTheoryComplete
