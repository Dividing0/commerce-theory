import CommerceTheory.Accounting

namespace CommerceTheory

/-! ## 6. Marketplace sales, listings, feeds, fees, and payouts -/

/-!
Marketplace listings connect internal catalog and inventory state to external
sales channels. The proof fields ensure published stock and payout calculations
stay within the internal source-of-truth limits.
-/

/-- Closed set of cases for `Marketplace` in the commerce domain model. -/
inductive Marketplace where
  | AmazonLike
  | RozetkaLike
  | EtsyLike
  | EbayLike
  | Custom
deriving DecidableEq, Repr

/-- Closed set of cases for `SalesChannel` in the commerce domain model. -/
inductive SalesChannel where
  | OwnWebsite
  | MarketplaceChannel : Marketplace → SalesChannel
  | B2BPortal
  | DropshipFeed
deriving DecidableEq, Repr

/-- Closed set of cases for `ListingStatus` in the commerce domain model. -/
inductive ListingStatus where
  | Draft
  | Active
  | Paused
  | Archived
deriving DecidableEq, Repr

/-- Data shape for `MarketplaceListing`; proof fields record invariants when needed. -/
structure MarketplaceListing where
  sku : Sku
  marketplace : Marketplace
  externalId : Nat
  price : Money
  currency : Currency
  publishedStock : Quantity
  status : ListingStatus

/-- Computes or checks `listingActive` using the validated data in this module. -/
def listingActive (listing : MarketplaceListing) : Prop :=
  listing.status = ListingStatus.Active

/-- Computes or checks `listingInStock` using the validated data in this module. -/
def listingInStock (listing : MarketplaceListing) : Prop :=
  0 < listing.publishedStock

/-- Computes or checks `listingCanBeAdvertised` using the validated data in this module. -/
def listingCanBeAdvertised (listing : MarketplaceListing) : Prop :=
  listingActive listing ∧ listingInStock listing

/-- States the safety property captured by `listingCanBeAdvertised_implies_active`. -/
theorem listingCanBeAdvertised_implies_active
    (listing : MarketplaceListing) (h : listingCanBeAdvertised listing) :
    listingActive listing := by
  exact h.left

/-- Advertisable listings must also publish positive stock. -/
theorem listingCanBeAdvertised_implies_in_stock
    (listing : MarketplaceListing) (h : listingCanBeAdvertised listing) :
    listingInStock listing := by
  exact h.right

/-- Data shape for `SyncedMarketplaceListing`; proof fields record invariants when needed. -/
structure SyncedMarketplaceListing where
  listing : MarketplaceListing
  stock : StockState
  same_sku : listing.sku = stock.sku
  publishedStock_le_available : listing.publishedStock ≤ availableStock stock

/-- States the safety property captured by `syncedListing_stock_is_safe`. -/
theorem syncedListing_stock_is_safe (s : SyncedMarketplaceListing) :
    s.listing.publishedStock ≤ availableStock s.stock := by
  exact s.publishedStock_le_available

/-- Synced marketplace listings point at the same SKU as internal stock. -/
theorem syncedListing_same_sku (s : SyncedMarketplaceListing) :
    s.listing.sku = s.stock.sku := by
  exact s.same_sku

/-- Published marketplace stock is also bounded by total internal stock. -/
theorem syncedListing_publishedStock_le_total (s : SyncedMarketplaceListing) :
    s.listing.publishedStock ≤ s.stock.total := by
  exact s.publishedStock_le_available.trans (availableStock_le_total s.stock)

/-- Data shape for `ChannelPricePolicy`; proof fields record invariants when needed. -/
structure ChannelPricePolicy where
  minPrice : Money
  maxPrice : Money
  min_le_max : minPrice ≤ maxPrice

/-- Computes or checks `validChannelPrice` using the validated data in this module. -/
def validChannelPrice (policy : ChannelPricePolicy) (price : Money) : Prop :=
  policy.minPrice ≤ price ∧ price ≤ policy.maxPrice

/-- Valid channel prices respect the policy minimum. -/
theorem validChannelPrice_ge_min
    (policy : ChannelPricePolicy) (price : Money)
    (h : validChannelPrice policy price) :
    policy.minPrice ≤ price := by
  exact h.left

/-- Valid channel prices respect the policy maximum. -/
theorem validChannelPrice_le_max
    (policy : ChannelPricePolicy) (price : Money)
    (h : validChannelPrice policy price) :
    price ≤ policy.maxPrice := by
  exact h.right

/-- Data shape for `SafeProductFeedLine`; proof fields record invariants when needed. -/
structure SafeProductFeedLine where
  sku : Sku
  channel : SalesChannel
  price : Money
  currency : Currency
  stock : Quantity
  stockState : StockState
  pricePolicy : ChannelPricePolicy
  same_sku : sku = stockState.sku
  price_valid : validChannelPrice pricePolicy price
  stock_safe : stock ≤ availableStock stockState

/-- States the safety property captured by `safeFeed_stock_le_available`. -/
theorem safeFeed_stock_le_available (f : SafeProductFeedLine) :
    f.stock ≤ availableStock f.stockState := by
  exact f.stock_safe

/-- Safe product feed lines preserve SKU identity with the stock source. -/
theorem safeFeed_same_sku (f : SafeProductFeedLine) :
    f.sku = f.stockState.sku := by
  exact f.same_sku

/-- Safe product feed prices respect the channel minimum. -/
theorem safeFeed_price_ge_min (f : SafeProductFeedLine) :
    f.pricePolicy.minPrice ≤ f.price := by
  exact f.price_valid.left

/-- Safe product feed prices respect the channel maximum. -/
theorem safeFeed_price_le_max (f : SafeProductFeedLine) :
    f.price ≤ f.pricePolicy.maxPrice := by
  exact f.price_valid.right

/-- Data shape for `MarketplaceFeeLedger`; proof fields record invariants when needed. -/
structure MarketplaceFeeLedger where
  gross : Money
  fee : Money
  payout : Money
  fee_le_gross : fee ≤ gross
  payout_correct : payout = gross - fee

/-- States the safety property captured by `marketplacePayout_le_gross`. -/
theorem marketplacePayout_le_gross (ledger : MarketplaceFeeLedger) :
    ledger.payout ≤ ledger.gross := by
  rw [ledger.payout_correct]
  exact Nat.sub_le ledger.gross ledger.fee

/-- States the safety property captured by `marketplacePayout_plus_fee_eq_gross`. -/
theorem marketplacePayout_plus_fee_eq_gross (ledger : MarketplaceFeeLedger) :
    ledger.payout + ledger.fee = ledger.gross := by
  rw [ledger.payout_correct]
  exact Nat.sub_add_cancel ledger.fee_le_gross

/-- Data shape for `MarketplaceOrder`; proof fields record invariants when needed. -/
structure MarketplaceOrder where
  marketplace : Marketplace
  externalOrderId : MarketplaceOrderId
  internalOrder : Order
  grossFromMarketplace : Money
  feeLedger : MarketplaceFeeLedger
  gross_matches_internal_total : grossFromMarketplace = internalOrder.total
  feeLedger_gross_matches : feeLedger.gross = grossFromMarketplace

/-- States the safety property captured by `marketplaceOrder_payout_le_internal_total`. -/
theorem marketplaceOrder_payout_le_internal_total (mo : MarketplaceOrder) :
    mo.feeLedger.payout ≤ mo.internalOrder.total := by
  calc
    mo.feeLedger.payout ≤ mo.feeLedger.gross := marketplacePayout_le_gross mo.feeLedger
    _ = mo.grossFromMarketplace := mo.feeLedger_gross_matches
    _ = mo.internalOrder.total := mo.gross_matches_internal_total

/-- Marketplace order gross revenue matches the internal order total. -/
theorem marketplaceOrder_gross_eq_internal_total (mo : MarketplaceOrder) :
    mo.grossFromMarketplace = mo.internalOrder.total := by
  exact mo.gross_matches_internal_total

/-- Marketplace payout plus marketplace fee recovers the internal order total. -/
theorem marketplaceOrder_payout_plus_fee_eq_internal_total (mo : MarketplaceOrder) :
    mo.feeLedger.payout + mo.feeLedger.fee = mo.internalOrder.total := by
  calc
    mo.feeLedger.payout + mo.feeLedger.fee = mo.feeLedger.gross :=
      marketplacePayout_plus_fee_eq_gross mo.feeLedger
    _ = mo.grossFromMarketplace := mo.feeLedger_gross_matches
    _ = mo.internalOrder.total := mo.gross_matches_internal_total


end CommerceTheory
