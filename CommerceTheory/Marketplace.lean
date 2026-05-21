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

/-- Marketplace fee calculation with an explicit rounding mode. -/
def marketplaceFeeRounded (mode : RoundingMode) (gross : Money) (feeRate : BasisPoints) :
    Money :=
  roundBpsAmount mode gross feeRate

/-- Marketplace payout calculation with an explicit rounding mode. -/
def marketplacePayoutRounded (mode : RoundingMode) (gross : Money) (payoutRate : BasisPoints) :
    Money :=
  roundBpsAmount mode gross payoutRate

/-- Data shape for `MarketplaceFeeLedger`; proof fields record invariants when needed. -/
structure MarketplaceFeeLedger where
  gross : Money
  feeRate : BasisPoints
  feeRoundingMode : RoundingMode
  fee : Money
  payout : Money
  fee_correct : fee = marketplaceFeeRounded feeRoundingMode gross feeRate
  fee_le_gross : fee ≤ gross
  payout_correct : payout = gross - fee

/-- Marketplace fees expose their declared rounding mode. -/
theorem marketplaceFeeLedger_uses_declared_rounding (ledger : MarketplaceFeeLedger) :
    ledger.fee = marketplaceFeeRounded ledger.feeRoundingMode ledger.gross ledger.feeRate := by
  exact ledger.fee_correct

/-- Floor marketplace-fee rounding error is bounded by one minor unit. -/
theorem marketplaceFee_floor_rounding_error_lt_one_minor_unit
    (gross : Money) (feeRate : BasisPoints) :
    floorRoundingRemainder (gross * feeRate.value) 10000 < 10000 := by
  exact floorRoundingRemainder_lt_denominator
    (gross * feeRate.value) 10000 (by norm_num)

/-- Marketplace-fee line/item floor-rounding error is bounded by one minor unit per line. -/
theorem marketplaceFeeLines_floor_rounding_error_le_one_minor_unit_per_line
    (grosses : List Money) (feeRate : BasisPoints) :
    floorRoundedLinesRemainderTotal 10000
        (grosses.map (fun gross => gross * feeRate.value)) ≤
      grosses.length * 10000 := by
  simpa using
    floorRoundedLinesRemainderTotal_le_one_minor_unit_per_line
      10000 (grosses.map (fun gross => gross * feeRate.value))
      (by norm_num)

/-- Data shape for `MarketplacePayoutCalculation`; proof fields record invariants when needed. -/
structure MarketplacePayoutCalculation where
  gross : Money
  payoutRate : BasisPoints
  payoutRoundingMode : RoundingMode
  payout : Money
  payout_correct : payout = marketplacePayoutRounded payoutRoundingMode gross payoutRate

/-- Marketplace payouts expose their declared rounding mode. -/
theorem marketplacePayout_uses_declared_rounding (payout : MarketplacePayoutCalculation) :
    payout.payout =
      marketplacePayoutRounded payout.payoutRoundingMode payout.gross payout.payoutRate := by
  exact payout.payout_correct

/-- Floor marketplace-payout rounding error is bounded by one minor unit. -/
theorem marketplacePayout_floor_rounding_error_lt_one_minor_unit
    (gross : Money) (payoutRate : BasisPoints) :
    floorRoundingRemainder (gross * payoutRate.value) 10000 < 10000 := by
  exact floorRoundingRemainder_lt_denominator
    (gross * payoutRate.value) 10000 (by norm_num)

/-- Marketplace-payout line/item floor-rounding error is bounded by one minor unit per line. -/
theorem marketplacePayoutLines_floor_rounding_error_le_one_minor_unit_per_line
    (grosses : List Money) (payoutRate : BasisPoints) :
    floorRoundedLinesRemainderTotal 10000
        (grosses.map (fun gross => gross * payoutRate.value)) ≤
      grosses.length * 10000 := by
  simpa using
    floorRoundedLinesRemainderTotal_le_one_minor_unit_per_line
      10000 (grosses.map (fun gross => gross * payoutRate.value))
      (by norm_num)

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
