import CommerceTheory.EventLanguage
import CommerceTheory.EventReplay
import CommerceTheory.ImplicitInvariants
import CommerceTheory.InventoryAlgorithms
import CommerceTheory.KeyedTotals
import CommerceTheory.OpportunityRanking
import CommerceTheory.Tax
import CommerceTheory.Workflow

namespace CommerceTheory

/-! ## Executable validators for proof-carrying records -/

/-!
External API, database, and file-import boundaries usually provide plain data,
not Lean evidence.  This module adds executable validators that turn raw records
into the existing proof-carrying domain structures when their decidable checks
pass.
-/

/-- Validation failures produced while converting raw data into safe records. -/
inductive ValidationError where
  | lineDiscountExceedsGross
  | shippingUnavailable
  | orderTotalMismatch
  | stockReservedExceedsTotal
  | pricePolicyInvalid
  | feedSkuMismatch
  | feedPriceOutOfPolicy
  | feedStockUnavailable
  | ledgerRefundedExceedsCaptured
  | refundExceedsRemaining
  | basisPointsOutOfRange
  | catalogInvariantFailed
  | inventoryInvariantFailed
  | accountingInvariantFailed
  | marketplaceInvariantFailed
  | marketingInvariantFailed
  | b2bInvariantFailed
  | dropshippingInvariantFailed
  | profitInvariantFailed
  | competitorInvariantFailed
  | merchandisingInvariantFailed
  | financeInvariantFailed
  | auditPermissionDenied
  | eventStreamInvalid
  | postPurchaseInvariantFailed
  | supplierQualityInvalid
  | opportunityInvariantFailed
  | crmInvariantFailed
  | logisticsInvariantFailed
  | implicitInvariantFailed
  | taxInvariantFailed
deriving DecidableEq, Repr

/-- Raw cart line data before the discount bound has been checked. -/
structure RawCartLine where
  sku : Sku
  price : Money
  cost : Money
  quantity : Quantity
  discount : Money
  weight : Weight

/-- Validate a raw cart line by checking that its discount fits inside gross value. -/
def validateCartLine (raw : RawCartLine) : Except ValidationError CartLine :=
  if hDiscount : raw.discount ≤ raw.price * raw.quantity then
    Except.ok
      { sku := raw.sku
        price := raw.price
        cost := raw.cost
        quantity := raw.quantity
        discount := raw.discount
        weight := raw.weight
        discount_le_gross := hDiscount }
  else
    Except.error ValidationError.lineDiscountExceedsGross

/-- Successful cart-line validation returns a line whose discount is bounded. -/
theorem validateCartLine_sound
    {raw : RawCartLine} {line : CartLine}
    (_h : validateCartLine raw = Except.ok line) :
    line.discount ≤ line.price * line.quantity := by
  exact line.discount_le_gross

/-- Validate all cart lines in order, stopping at the first failed line. -/
def validateCartLines : List RawCartLine → Except ValidationError (List CartLine)
  | [] => Except.ok []
  | raw :: rest => do
      let line ← validateCartLine raw
      let lines ← validateCartLines rest
      Except.ok (line :: lines)

/-- Raw order data before shipping capacity and total calculation are checked. -/
structure RawOrder where
  id : OrderId
  items : List RawCartLine
  couponAmount : Money
  shippingMethod : ShippingMethod
  tax : Money
  currency : Currency
  status : OrderStatus
  total : Money

/-- Validate a raw order by checking its lines, shipping capacity, and computed total. -/
def validateOrder (raw : RawOrder) : Except ValidationError Order := do
  let items ← validateCartLines raw.items
  if hShipping : shippingAvailable raw.shippingMethod (cartWeightTotal items) then
    if hTotal :
        raw.total = orderTotal raw.shippingMethod raw.couponAmount raw.tax items then
      Except.ok
        { id := raw.id
          items := items
          couponAmount := raw.couponAmount
          shippingMethod := raw.shippingMethod
          tax := raw.tax
          currency := raw.currency
          status := raw.status
          total := raw.total
          shipping_available := hShipping
          total_correct := hTotal }
    else
      Except.error ValidationError.orderTotalMismatch
  else
    Except.error ValidationError.shippingUnavailable

/-- Successful order validation returns an order with the standard pricing bound. -/
theorem validateOrder_sound
    {raw : RawOrder} {order : Order}
    (_h : validateOrder raw = Except.ok order) :
    order.total ≤
      cartGrossTotal order.items + order.shippingMethod.price + order.tax := by
  exact order_total_is_safe order

/-- Successful order validation returns an order whose stored total is computed. -/
theorem validateOrder_total_matches_calculation
    {raw : RawOrder} {order : Order}
    (_h : validateOrder raw = Except.ok order) :
    order.total =
      orderTotal order.shippingMethod order.couponAmount order.tax order.items := by
  exact order.total_correct

/-- Raw stock data before the reservation bound has been checked. -/
structure RawStockState where
  sku : Sku
  total : Quantity
  reserved : Quantity

/-- Validate raw stock by checking reservations do not exceed total stock. -/
def validateStockState (raw : RawStockState) :
    Except ValidationError StockState :=
  if hReserved : raw.reserved ≤ raw.total then
    Except.ok
      { sku := raw.sku
        total := raw.total
        reserved := raw.reserved
        reserved_le_total := hReserved }
  else
    Except.error ValidationError.stockReservedExceedsTotal

/-- Successful stock validation returns a stock state with safe reservations. -/
theorem validateStockState_sound
    {raw : RawStockState} {stock : StockState}
    (_h : validateStockState raw = Except.ok stock) :
    stock.reserved ≤ stock.total := by
  exact stock.reserved_le_total

/-- Raw channel price policy before min/max ordering has been checked. -/
structure RawChannelPricePolicy where
  minPrice : Money
  maxPrice : Money

/-- Validate a raw channel price policy by checking its interval is nonempty. -/
def validateChannelPricePolicy (raw : RawChannelPricePolicy) :
    Except ValidationError ChannelPricePolicy :=
  if hMinLeMax : raw.minPrice ≤ raw.maxPrice then
    Except.ok
      { minPrice := raw.minPrice
        maxPrice := raw.maxPrice
        min_le_max := hMinLeMax }
  else
    Except.error ValidationError.pricePolicyInvalid

/-- Successful price-policy validation returns an ordered price interval. -/
theorem validateChannelPricePolicy_sound
    {raw : RawChannelPricePolicy} {policy : ChannelPricePolicy}
    (_h : validateChannelPricePolicy raw = Except.ok policy) :
    policy.minPrice ≤ policy.maxPrice := by
  exact policy.min_le_max

/-- Raw feed-line data before stock, SKU, and price-policy checks. -/
structure RawProductFeedLine where
  sku : Sku
  channel : SalesChannel
  price : Money
  currency : Currency
  stock : Quantity
  stockState : RawStockState
  pricePolicy : RawChannelPricePolicy

/-- Validate a raw product feed line into the existing safe marketplace feed shape. -/
def validateFeedLine (raw : RawProductFeedLine) :
    Except ValidationError SafeProductFeedLine := do
  let stockState ← validateStockState raw.stockState
  let pricePolicy ← validateChannelPricePolicy raw.pricePolicy
  if hSku : raw.sku = stockState.sku then
    if hPrice : validChannelPrice pricePolicy raw.price then
      if hStock : raw.stock ≤ availableStock stockState then
        Except.ok
          { sku := raw.sku
            channel := raw.channel
            price := raw.price
            currency := raw.currency
            stock := raw.stock
            stockState := stockState
            pricePolicy := pricePolicy
            same_sku := hSku
            price_valid := hPrice
            stock_safe := hStock }
      else
        Except.error ValidationError.feedStockUnavailable
    else
      Except.error ValidationError.feedPriceOutOfPolicy
  else
    Except.error ValidationError.feedSkuMismatch

/-- Successful feed-line validation returns SKU, stock, and price-policy safety. -/
theorem validateFeedLine_sound
    {raw : RawProductFeedLine} {line : SafeProductFeedLine}
    (_h : validateFeedLine raw = Except.ok line) :
    line.sku = line.stockState.sku ∧
      line.pricePolicy.minPrice ≤ line.price ∧
      line.price ≤ line.pricePolicy.maxPrice ∧
      line.stock ≤ availableStock line.stockState := by
  exact ⟨line.same_sku, line.price_valid.left, line.price_valid.right,
    line.stock_safe⟩

/-- Raw payment-ledger data before cumulative refund safety has been checked. -/
structure RawPaymentLedger where
  captured : Money
  refunded : Money

/-- Validate a raw ledger by checking cumulative refunds do not exceed capture. -/
def validatePaymentLedger (raw : RawPaymentLedger) :
    Except ValidationError PaymentLedger :=
  if hRefunded : raw.refunded ≤ raw.captured then
    Except.ok
      { captured := raw.captured
        refunded := raw.refunded
        refunded_le_captured := hRefunded }
  else
    Except.error ValidationError.ledgerRefundedExceedsCaptured

/-- Successful ledger validation returns a ledger with bounded cumulative refunds. -/
theorem validatePaymentLedger_sound
    {raw : RawPaymentLedger} {ledger : PaymentLedger}
    (_h : validatePaymentLedger raw = Except.ok ledger) :
    ledger.refunded ≤ ledger.captured := by
  exact ledger.refunded_le_captured

/-- Raw refund request before the ledger remaining-balance check. -/
structure RawRefund where
  amount : Money

/-- A refund request paired with evidence that it fits inside a payment ledger. -/
structure ValidRefund where
  ledger : PaymentLedger
  amount : Money
  refundable : canRefund ledger amount

/-- Validate a refund request against an already-validated payment ledger. -/
def validateRefund (raw : RawRefund) (ledger : PaymentLedger) :
    Except ValidationError ValidRefund :=
  if hRefund : canRefund ledger raw.amount then
    Except.ok
      { ledger := ledger
        amount := raw.amount
        refundable := hRefund }
  else
    Except.error ValidationError.refundExceedsRemaining

/-- Successful refund validation returns an amount bounded by the remaining balance. -/
theorem validateRefund_sound
    {raw : RawRefund} {ledger : PaymentLedger} {refund : ValidRefund}
    (_h : validateRefund raw ledger = Except.ok refund) :
    refund.amount ≤ remainingRefundAmount refund.ledger := by
  exact canRefund_amount_le_remaining
    refund.ledger refund.amount refund.refundable

/-- Issue a validated refund using the existing ledger transition. -/
def issueValidRefund (refund : ValidRefund) : PaymentLedger :=
  issueRefund refund.ledger refund.amount refund.refundable

/-- Issuing a successfully validated refund preserves the payment-ledger cap. -/
theorem validateRefund_issue_preserves_safety
    {raw : RawRefund} {ledger : PaymentLedger} {refund : ValidRefund}
    (_h : validateRefund raw ledger = Except.ok refund) :
    (issueValidRefund refund).refunded ≤ (issueValidRefund refund).captured := by
  exact issueRefund_preserves_safety
    refund.ledger refund.amount refund.refundable

/-! ### Foundation, catalog, and inventory validators -/

/-- Validate a basis-point rate by checking it is no larger than 100%. -/
def validateBasisPoints (value : Nat) : Except ValidationError BasisPoints :=
  if hValue : value ≤ 10000 then
    Except.ok { value := value, value_le_10000 := hValue }
  else
    Except.error ValidationError.basisPointsOutOfRange

/-- Successful basis-point validation returns a bounded rate. -/
theorem validateBasisPoints_sound
    {value : Nat} {bps : BasisPoints}
    (_h : validateBasisPoints value = Except.ok bps) :
    bps.value ≤ 10000 := by
  exact bps.value_le_10000

/-- Validate that a catalog variant belongs to its product. -/
def validateProductCatalogEntry
    (product : Product) (variant : ProductVariant) :
    Except ValidationError ProductCatalogEntry :=
  if hBelongs : variant.productId = product.id then
    Except.ok
      { product := product
        variant := variant
        variant_belongs_to_product := hBelongs }
  else
    Except.error ValidationError.catalogInvariantFailed

/-- Successful catalog-entry validation returns product/variant identity evidence. -/
theorem validateProductCatalogEntry_sound
    {product : Product} {variant : ProductVariant} {entry : ProductCatalogEntry}
    (_h : validateProductCatalogEntry product variant = Except.ok entry) :
    entry.variant.productId = entry.product.id := by
  exact entry.variant_belongs_to_product

/-- Validate marketplace listing content against a content policy. -/
def validateListingContent
    (content : ListingContent) (policy : MarketplaceContentPolicy) :
    Except ValidationError ValidListingContent :=
  if hTitle : content.titleLength ≤ policy.maxTitleLength then
    if hImages : policy.minImageCount ≤ content.imageCount then
      if hAttrs : content.requiredAttributesFilled = true then
        Except.ok
          { content := content
            policy := policy
            title_ok := hTitle
            images_ok := hImages
            attrs_ok := hAttrs }
      else
        Except.error ValidationError.catalogInvariantFailed
    else
      Except.error ValidationError.catalogInvariantFailed
  else
    Except.error ValidationError.catalogInvariantFailed

/-- Successful listing-content validation returns the compact policy proof. -/
theorem validateListingContent_sound
    {content : ListingContent} {policy : MarketplaceContentPolicy}
    {valid : ValidListingContent}
    (_h : validateListingContent content policy = Except.ok valid) :
    valid.content.titleLength ≤ valid.policy.maxTitleLength ∧
      valid.policy.minImageCount ≤ valid.content.imageCount ∧
      valid.content.requiredAttributesFilled = true := by
  exact validListingContent_policy_ok valid

/-- Validate stock and attach an optimistic-locking version. -/
def validateVersionedStock (raw : RawStockState) (version : Nat) :
    Except ValidationError VersionedStock := do
  let stock ← validateStockState raw
  Except.ok
    { sku := stock.sku
      total := stock.total
      reserved := stock.reserved
      reserved_le_total := stock.reserved_le_total
      version := version }

/-- Validate a warehouse pick task against the bin quantity. -/
def validatePickTask (sku : Sku) (requested : Quantity) (bin : BinStock) :
    Except ValidationError PickTask :=
  if hRequested : requested ≤ bin.quantity then
    Except.ok
      { sku := sku
        requested := requested
        bin := bin
        requested_le_bin_qty := hRequested }
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Validate a pack task against the quantity picked. -/
def validatePackTask (picked packed : Quantity) :
    Except ValidationError PackTask :=
  if hPacked : packed ≤ picked then
    Except.ok
      { picked := picked
        packed := packed
        packed_le_picked := hPacked }
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Validate a warehouse shipment against the packed quantity. -/
def validateWarehouseShipment (packed shipped : Quantity) :
    Except ValidationError WarehouseShipment :=
  if hShipped : shipped ≤ packed then
    Except.ok
      { packed := packed
        shipped := shipped
        shipped_le_packed := hShipped }
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Validate an allocation against the node's available stock. -/
def validateAllocation (node : InventoryNode) (quantity : Quantity) :
    Except ValidationError Allocation :=
  if hQuantity : quantity ≤ availableStock node.stock then
    Except.ok
      { node := node
        quantity := quantity
        quantity_le_available := hQuantity }
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful allocation validation returns the available-stock bound. -/
theorem validateAllocation_sound
    {node : InventoryNode} {quantity : Quantity} {allocation : Allocation}
    (_h : validateAllocation node quantity = Except.ok allocation) :
    allocation.quantity ≤ availableStock allocation.node.stock := by
  exact allocation.quantity_le_available

/-- Validate a fulfillment plan by checking allocated quantity equals request. -/
def validateFulfillmentPlan
    (requested : Quantity) (allocations : List Allocation) :
    Except ValidationError FulfillmentPlan :=
  if hTotal : allocationsTotal allocations = requested then
    Except.ok
      { requested := requested
        allocations := allocations
        total_eq_requested := hTotal }
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Validate a fulfillment plan and require distinct warehouse/SKU allocation keys. -/
def validateDistinctFulfillmentPlan
    (requested : Quantity) (allocations : List Allocation) :
    Except ValidationError DistinctFulfillmentPlan :=
  if hTotal : allocationsTotal allocations = requested then
    if hKeys : allocationKeysDistinct allocations then
      Except.ok
        { requested := requested
          allocations := allocations
          total_eq_requested := hTotal
          allocation_keys_distinct := hKeys }
    else
      Except.error ValidationError.inventoryInvariantFailed
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful distinct fulfillment-plan validation proves the request is stock-safe. -/
theorem validateDistinctFulfillmentPlan_sound
    {requested : Quantity} {allocations : List Allocation}
    {plan : DistinctFulfillmentPlan}
    (_h : validateDistinctFulfillmentPlan requested allocations = Except.ok plan) :
    plan.requested ≤ allocationsAvailableTotal plan.allocations ∧
      allocationKeysDistinct plan.allocations := by
  exact ⟨distinctFulfillmentPlan_requested_le_availableTotal plan,
    plan.allocation_keys_distinct⟩

/-! ### Inventory concurrency validators -/

/-- Raw reservation attempt before stock, version, and CAS checks. -/
structure RawReservationAttempt where
  stock : RawStockState
  version : Nat
  quantity : Quantity
  expectedVersion : Nat

/-- Validate a raw reservation attempt into versioned stock plus observed version. -/
def validateRawReservationAttempt (raw : RawReservationAttempt) :
    Except ValidationError ReservationAttempt := do
  let stock ← validateVersionedStock raw.stock raw.version
  Except.ok
    { stock := stock
      quantity := raw.quantity
      expectedVersion := raw.expectedVersion }

/-- Successful raw reservation-attempt validation carries safe versioned stock. -/
theorem validateRawReservationAttempt_sound
    {raw : RawReservationAttempt} {attempt : ReservationAttempt}
    (_h : validateRawReservationAttempt raw = Except.ok attempt) :
    attempt.stock.reserved ≤ attempt.stock.total := by
  exact attempt.stock.reserved_le_total

/-- Validate a compare-and-swap reservation and return the next versioned state. -/
def validateCompareAndSwapReservation
    (stock : VersionedStock) (quantity expectedVersion : Nat) :
    Except ValidationError VersionedStock :=
  match compareAndSwapReserve? stock quantity expectedVersion with
  | some next => Except.ok next
  | none => Except.error ValidationError.inventoryInvariantFailed

/-- Successful CAS validation advances the version and preserves stock safety. -/
theorem validateCompareAndSwapReservation_sound
    {stock next : VersionedStock} {quantity expectedVersion : Nat}
    (h : validateCompareAndSwapReservation stock quantity expectedVersion =
      Except.ok next) :
    next.version = stock.version + 1 ∧ next.reserved ≤ next.total := by
  cases hCas : compareAndSwapReserve? stock quantity expectedVersion with
  | none =>
      simp [validateCompareAndSwapReservation, hCas] at h
  | some result =>
      simp [validateCompareAndSwapReservation, hCas] at h
      cases h
      exact ⟨compareAndSwapReserve?_success_increases_version
          stock quantity expectedVersion result hCas,
        compareAndSwapReserve?_success_preserves_safety
          stock quantity expectedVersion result hCas⟩

/-- Validate a raw reservation attempt and execute it with CAS semantics. -/
def validateRawCompareAndSwapReservation (raw : RawReservationAttempt) :
    Except ValidationError VersionedStock := do
  let attempt ← validateRawReservationAttempt raw
  validateCompareAndSwapReservation
    attempt.stock attempt.quantity attempt.expectedVersion

/-- Validate release of reserved stock. -/
def validateReleaseReservedStock (stock : StockState) (quantity : Quantity) :
    Except ValidationError StockState :=
  if hReserved : quantity ≤ stock.reserved then
    Except.ok (releaseReservedStock stock quantity hReserved)
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful release validation preserves stock safety. -/
theorem validateReleaseReservedStock_sound
    {stock released : StockState} {quantity : Quantity}
    (_h : validateReleaseReservedStock stock quantity = Except.ok released) :
    released.reserved ≤ released.total := by
  exact released.reserved_le_total

/-- Validate shipment confirmation from already-reserved stock. -/
def validateConfirmReservedShipment (stock : StockState) (quantity : Quantity) :
    Except ValidationError StockState :=
  if hReserved : quantity ≤ stock.reserved then
    Except.ok (confirmReservedShipment stock quantity hReserved)
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful reserved-shipment confirmation preserves safety. -/
theorem validateConfirmReservedShipment_sound
    {stock confirmed : StockState} {quantity : Quantity}
    (_h : validateConfirmReservedShipment stock quantity = Except.ok confirmed) :
    confirmed.reserved ≤ confirmed.total := by
  exact confirmed.reserved_le_total

/-- Validate timed reservation expiry and reserved quantity evidence. -/
def validateTimedReservation
    (stock : StockState) (quantity : Quantity)
    (reservedAt expiresAt : Timestamp) (status : ReservationStatus) :
    Except ValidationError TimedReservation :=
  if hWindow : reservedAt ≤ expiresAt then
    if hQuantity : quantity ≤ stock.reserved then
      Except.ok
        { stock := stock
          quantity := quantity
          reservedAt := reservedAt
          expiresAt := expiresAt
          status := status
          reserved_at_le_expires := hWindow
          quantity_le_reserved := hQuantity }
    else
      Except.error ValidationError.inventoryInvariantFailed
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful timed-reservation validation exposes its time and quantity bounds. -/
theorem validateTimedReservation_sound
    {stock : StockState} {quantity : Quantity}
    {reservedAt expiresAt : Timestamp} {status : ReservationStatus}
    {reservation : TimedReservation}
    (_h :
      validateTimedReservation stock quantity reservedAt expiresAt status =
        Except.ok reservation) :
    reservation.reservedAt ≤ reservation.expiresAt ∧
      reservation.quantity ≤ reservation.stock.reserved := by
  exact ⟨reservation.reserved_at_le_expires, reservation.quantity_le_reserved⟩

/-- Validate release of an expired timed reservation. -/
def validateReleaseExpiredReservation
    (reservation : TimedReservation) (now : Timestamp) :
    Except ValidationError StockState :=
  if hExpired : reservationExpiredAt now reservation then
    Except.ok (releaseExpiredReservation reservation now hExpired)
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful expired-reservation release preserves stock safety. -/
theorem validateReleaseExpiredReservation_sound
    {reservation : TimedReservation} {now : Timestamp} {stock : StockState}
    (_h : validateReleaseExpiredReservation reservation now = Except.ok stock) :
    stock.reserved ≤ stock.total := by
  exact stock.reserved_le_total

/-- Validate a backorder split between immediate and delayed quantity. -/
def validateBackorderRequest
    (sku : Sku) (requested availableNow backordered : Quantity) :
    Except ValidationError BackorderRequest :=
  if hTotal : requested = availableNow + backordered then
    Except.ok
      { sku := sku
        requested := requested
        availableNow := availableNow
        backordered := backordered
        requested_eq_available_plus_backordered := hTotal }
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful backorder validation conserves requested quantity. -/
theorem validateBackorderRequest_sound
    {request : BackorderRequest}
    (_h :
      validateBackorderRequest request.sku request.requested
        request.availableNow request.backordered = Except.ok request) :
    request.availableNow + request.backordered = request.requested ∧
      request.backordered ≤ request.requested := by
  exact ⟨backorderRequest_conserves_quantity request,
    backorderRequest_backordered_le_requested request⟩

/-- Validate preorder window ordering. -/
def validatePreorderWindow
    (sku : Sku) (opensAt closesAt : Timestamp) (capacity : Quantity) :
    Except ValidationError PreorderWindow :=
  if hWindow : opensAt ≤ closesAt then
    Except.ok
      { sku := sku
        opensAt := opensAt
        closesAt := closesAt
        capacity := capacity
        opens_le_closes := hWindow }
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful preorder-window validation exposes ordered window bounds. -/
theorem validatePreorderWindow_sound
    {window : PreorderWindow}
    (_h :
      validatePreorderWindow window.sku window.opensAt window.closesAt
        window.capacity = Except.ok window) :
    window.opensAt ≤ window.closesAt := by
  exact window.opens_le_closes

/-- Validate a preorder reservation against capacity and window timing. -/
def validatePreorderReservation
    (window : PreorderWindow) (quantity : Quantity) (reservedAt : Timestamp) :
    Except ValidationError PreorderReservation :=
  if hCapacity : quantity ≤ window.capacity then
    if hWindow : window.opensAt ≤ reservedAt ∧ reservedAt ≤ window.closesAt then
      Except.ok
        { window := window
          quantity := quantity
          reservedAt := reservedAt
          quantity_le_capacity := hCapacity
          reserved_in_window := hWindow }
    else
      Except.error ValidationError.inventoryInvariantFailed
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful preorder validation proves capacity and window membership. -/
theorem validatePreorderReservation_sound
    {reservation : PreorderReservation}
    (_h :
      validatePreorderReservation reservation.window reservation.quantity
        reservation.reservedAt = Except.ok reservation) :
    reservation.quantity ≤ reservation.window.capacity ∧
      reservation.window.opensAt ≤ reservation.reservedAt ∧
      reservation.reservedAt ≤ reservation.window.closesAt := by
  exact ⟨preorderReservation_quantity_le_capacity reservation,
    (preorderReservation_in_window reservation).left,
    (preorderReservation_in_window reservation).right⟩

/-- Validate uniqueness of serial-numbered inventory units. -/
def validateSerializedInventorySet (units : List SerializedInventoryUnit) :
    Except ValidationError SerializedInventorySet :=
  if hSerials : serialNumbersDistinct units then
    Except.ok
      { units := units
        serials_distinct := hSerials }
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful serialized-inventory validation proves unique serial numbers. -/
theorem validateSerializedInventorySet_sound
    {inventory : SerializedInventorySet}
    (_h : validateSerializedInventorySet inventory.units = Except.ok inventory) :
    serialNumbersDistinct inventory.units := by
  exact serializedInventorySet_serials_distinct inventory

/-- Validate that a lot is currently usable. -/
def validateUsableInventoryLot (lot : InventoryLot) (now : Timestamp) :
    Except ValidationError InventoryLot :=
  if _hUsable : lotUsableAt now lot then
    Except.ok lot
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful lot validation proves the lot is usable at the checked timestamp. -/
theorem validateUsableInventoryLot_sound
    {lot : InventoryLot} {now : Timestamp}
    (h : validateUsableInventoryLot lot now = Except.ok lot) :
    lotUsableAt now lot := by
  unfold validateUsableInventoryLot at h
  by_cases hUsable : lotUsableAt now lot
  · exact hUsable
  · simp [hUsable] at h

/-- Validate SKU substitution against available substitute stock. -/
def validateSkuSubstitution
    (requestedSku substituteSku : Sku) (substituteStock : StockState)
    (maxSubstituteQty : Quantity) :
    Except ValidationError SkuSubstitution :=
  if hSku : substituteStock.sku = substituteSku then
    if hAvailable : maxSubstituteQty ≤ availableStock substituteStock then
      Except.ok
        { requestedSku := requestedSku
          substituteSku := substituteSku
          substituteStock := substituteStock
          maxSubstituteQty := maxSubstituteQty
          substitute_sku_matches := hSku
          max_qty_le_substitute_available := hAvailable }
    else
      Except.error ValidationError.inventoryInvariantFailed
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful substitution validation proves substitute availability. -/
theorem validateSkuSubstitution_sound
    {rule : SkuSubstitution}
    (_h :
      validateSkuSubstitution rule.requestedSku rule.substituteSku
        rule.substituteStock rule.maxSubstituteQty = Except.ok rule) :
    rule.substituteStock.sku = rule.substituteSku ∧
      rule.maxSubstituteQty ≤ availableStock rule.substituteStock := by
  exact ⟨rule.substitute_sku_matches,
    skuSubstitution_max_qty_le_available rule⟩

/-- Validate a split fulfillment plan against two distinct warehouse witnesses. -/
def validateSplitFulfillmentPlan
    (plan : DistinctFulfillmentPlan)
    (firstWarehouse secondWarehouse : Warehouse) :
    Except ValidationError SplitFulfillmentPlan :=
  if hFirst : firstWarehouse.id ∈ allocationWarehouseIds plan.allocations then
    if hSecond : secondWarehouse.id ∈ allocationWarehouseIds plan.allocations then
      if hDistinct : firstWarehouse.id ≠ secondWarehouse.id then
        Except.ok
          { plan := plan
            firstWarehouse := firstWarehouse
            secondWarehouse := secondWarehouse
            first_warehouse_used := hFirst
            second_warehouse_used := hSecond
            warehouses_distinct := hDistinct }
      else
        Except.error ValidationError.inventoryInvariantFailed
    else
      Except.error ValidationError.inventoryInvariantFailed
  else
    Except.error ValidationError.inventoryInvariantFailed

/-- Successful split-fulfillment validation preserves aggregate stock safety. -/
theorem validateSplitFulfillmentPlan_sound
    {plan : SplitFulfillmentPlan}
    (_h :
      validateSplitFulfillmentPlan plan.plan plan.firstWarehouse
        plan.secondWarehouse = Except.ok plan) :
    plan.plan.requested ≤ allocationsAvailableTotal plan.plan.allocations ∧
      allocationKeysDistinct plan.plan.allocations ∧
      plan.firstWarehouse.id ≠ plan.secondWarehouse.id := by
  exact ⟨splitFulfillmentPlan_requested_le_availableTotal plan,
    splitFulfillmentPlan_allocation_keys_distinct plan,
    splitFulfillmentPlan_warehouses_distinct plan⟩

/-! ### Order, accounting, and marketplace validators -/

/-- Validate a typestate order by requiring a positive total. -/
def validateTypedOrder
    (status : OrderStatus) (id : OrderId) (total : Money) (currency : Currency) :
    Except ValidationError (TypedOrder status) :=
  if hTotal : 0 < total then
    Except.ok { id := id, total := total, currency := currency, total_pos := hTotal }
  else
    Except.error ValidationError.orderTotalMismatch

/-- Validate a typestate payment by requiring a positive amount. -/
def validateTypedPayment
    (state : PaymentState) (id : PaymentId) (orderId : OrderId)
    (amount : Money) (currency : Currency) :
    Except ValidationError (TypedPayment state) :=
  if hAmount : 0 < amount then
    Except.ok
      { id := id
        orderId := orderId
        amount := amount
        currency := currency
        amount_pos := hAmount }
  else
    Except.error ValidationError.orderTotalMismatch

/-- Validate a journal entry by checking debit and credit totals. -/
def validateBalancedJournalEntry (postings : List Posting) :
    Except ValidationError BalancedJournalEntry :=
  if hBalanced : debitTotal postings = creditTotal postings then
    Except.ok { postings := postings, balanced := hBalanced }
  else
    Except.error ValidationError.accountingInvariantFailed

/-- Successful journal validation returns double-entry balance. -/
theorem validateBalancedJournalEntry_sound
    {postings : List Posting} {entry : BalancedJournalEntry}
    (_h : validateBalancedJournalEntry postings = Except.ok entry) :
    debitTotal entry.postings = creditTotal entry.postings := by
  exact entry.balanced

/-- Validate a synced marketplace listing against internal stock. -/
def validateSyncedMarketplaceListing
    (listing : MarketplaceListing) (stock : StockState) :
    Except ValidationError SyncedMarketplaceListing :=
  if hSku : listing.sku = stock.sku then
    if hStock : listing.publishedStock ≤ availableStock stock then
      Except.ok
        { listing := listing
          stock := stock
          same_sku := hSku
          publishedStock_le_available := hStock }
    else
      Except.error ValidationError.marketplaceInvariantFailed
  else
    Except.error ValidationError.marketplaceInvariantFailed

/-- Validate a marketplace fee ledger with explicit rounding evidence. -/
def validateMarketplaceFeeLedger
    (gross : Money) (feeRate : BasisPoints) (feeRoundingMode : RoundingMode)
    (fee payout : Money) :
    Except ValidationError MarketplaceFeeLedger :=
  if hFee : fee = marketplaceFeeRounded feeRoundingMode gross feeRate then
    if hFeeLe : fee ≤ gross then
      if hPayout : payout = gross - fee then
        Except.ok
          { gross := gross
            feeRate := feeRate
            feeRoundingMode := feeRoundingMode
            fee := fee
            payout := payout
            fee_correct := hFee
            fee_le_gross := hFeeLe
            payout_correct := hPayout }
      else
        Except.error ValidationError.marketplaceInvariantFailed
    else
      Except.error ValidationError.marketplaceInvariantFailed
  else
    Except.error ValidationError.marketplaceInvariantFailed

/-- Successful marketplace-fee validation proves payout plus fee recovers gross. -/
theorem validateMarketplaceFeeLedger_sound
    {gross fee payout : Money} {feeRate : BasisPoints}
    {mode : RoundingMode} {ledger : MarketplaceFeeLedger}
    (_h :
      validateMarketplaceFeeLedger gross feeRate mode fee payout =
        Except.ok ledger) :
    ledger.payout + ledger.fee = ledger.gross := by
  exact marketplacePayout_plus_fee_eq_gross ledger

/-- Validate a marketplace payout calculation with explicit rounding evidence. -/
def validateMarketplacePayoutCalculation
    (gross : Money) (payoutRate : BasisPoints)
    (payoutRoundingMode : RoundingMode) (payout : Money) :
    Except ValidationError MarketplacePayoutCalculation :=
  if hPayout : payout = marketplacePayoutRounded payoutRoundingMode gross payoutRate then
    Except.ok
      { gross := gross
        payoutRate := payoutRate
        payoutRoundingMode := payoutRoundingMode
        payout := payout
        payout_correct := hPayout }
  else
    Except.error ValidationError.marketplaceInvariantFailed

/-- Validate a marketplace order bridge to its internal order and fee ledger. -/
def validateMarketplaceOrder
    (marketplace : Marketplace) (externalOrderId : MarketplaceOrderId)
    (internalOrder : Order) (grossFromMarketplace : Money)
    (feeLedger : MarketplaceFeeLedger) :
    Except ValidationError MarketplaceOrder :=
  if hGross : grossFromMarketplace = internalOrder.total then
    if hLedger : feeLedger.gross = grossFromMarketplace then
      Except.ok
        { marketplace := marketplace
          externalOrderId := externalOrderId
          internalOrder := internalOrder
          grossFromMarketplace := grossFromMarketplace
          feeLedger := feeLedger
          gross_matches_internal_total := hGross
          feeLedger_gross_matches := hLedger }
    else
      Except.error ValidationError.marketplaceInvariantFailed
  else
    Except.error ValidationError.marketplaceInvariantFailed

/-- Successful marketplace-order validation keeps payout inside the internal total. -/
theorem validateMarketplaceOrder_sound
    {marketplace : Marketplace} {externalOrderId : MarketplaceOrderId}
    {internalOrder : Order} {gross : Money}
    {ledger : MarketplaceFeeLedger} {order : MarketplaceOrder}
    (_h :
      validateMarketplaceOrder marketplace externalOrderId internalOrder gross ledger =
        Except.ok order) :
    order.feeLedger.payout ≤ order.internalOrder.total := by
  exact marketplaceOrder_payout_le_internal_total order

/-! ### Marketing and B2B validators -/

/-- Validate campaign budget and click-count bounds. -/
def validateMarketingCampaign
    (id : CampaignId) (platform : AdPlatform) (adType : AdType)
    (destination : AdDestination) (status : CampaignStatus)
    (budget spend : Money) (impressions clicks conversions : Nat)
    (attributedRevenue : Money) :
    Except ValidationError MarketingCampaign :=
  if hSpend : spend ≤ budget then
    if hClicks : clicks ≤ impressions then
      Except.ok
        { id := id
          platform := platform
          adType := adType
          destination := destination
          status := status
          budget := budget
          spend := spend
          impressions := impressions
          clicks := clicks
          conversions := conversions
          attributedRevenue := attributedRevenue
          spend_le_budget := hSpend
          clicks_le_impressions := hClicks }
    else
      Except.error ValidationError.marketingInvariantFailed
  else
    Except.error ValidationError.marketingInvariantFailed

/-- Validate that click-attributed conversions do not exceed clicks. -/
def validateClickAttributedCampaign (campaign : MarketingCampaign) :
    Except ValidationError ClickAttributedCampaign :=
  if hConversions : campaign.conversions ≤ campaign.clicks then
    Except.ok
      { campaign := campaign
        conversions_le_clicks := hConversions }
  else
    Except.error ValidationError.marketingInvariantFailed

/-- Validate monotone funnel counts. -/
def validateFunnel
    (visitors addToCart checkoutStarted purchases : Nat) :
    Except ValidationError Funnel :=
  if hAdd : addToCart ≤ visitors then
    if hCheckout : checkoutStarted ≤ addToCart then
      if hPurchases : purchases ≤ checkoutStarted then
        Except.ok
          { visitors := visitors
            addToCart := addToCart
            checkoutStarted := checkoutStarted
            purchases := purchases
            addToCart_le_visitors := hAdd
            checkout_le_addToCart := hCheckout
            purchases_le_checkout := hPurchases }
      else
        Except.error ValidationError.marketingInvariantFailed
    else
      Except.error ValidationError.marketingInvariantFailed
  else
    Except.error ValidationError.marketingInvariantFailed

/-- Successful funnel validation proves purchases cannot exceed visitors. -/
theorem validateFunnel_sound
    {visitors addToCart checkoutStarted purchases : Nat} {funnel : Funnel}
    (_h :
      validateFunnel visitors addToCart checkoutStarted purchases =
        Except.ok funnel) :
    funnel.purchases ≤ funnel.visitors := by
  exact funnel_purchases_le_visitors funnel

/-- Validate aggregate attribution credit against an order total. -/
def validateOrderAttributionLedger
    (order : Order) (credits : List AttributionCredit) :
    Except ValidationError OrderAttributionLedger :=
  if hTotal : attributionCreditTotal credits ≤ order.total then
    Except.ok
      { order := order
        credits := credits
        total_credits_le_order_total := hTotal }
  else
    Except.error ValidationError.marketingInvariantFailed

/-- Validate one experiment variant's conversion count. -/
def validateExperimentVariant
    (id : Id) (trafficWeight visitors conversions : Nat) :
    Except ValidationError ExperimentVariant :=
  if hConversions : conversions ≤ visitors then
    Except.ok
      { id := id
        trafficWeight := trafficWeight
        visitors := visitors
        conversions := conversions
        conversions_le_visitors := hConversions }
  else
    Except.error ValidationError.marketingInvariantFailed

/-- Validate that experiment traffic weights add up to 100. -/
def validateExperiment
    (id : Id) (variants : List ExperimentVariant) :
    Except ValidationError Experiment :=
  if hTraffic : experimentTrafficTotal variants = 100 then
    Except.ok
      { id := id
        variants := variants
        traffic_total_100 := hTraffic }
  else
    Except.error ValidationError.marketingInvariantFailed

/-- Validate a trade price-book entry's margins and wholesale minimum. -/
def validateTradePriceBookEntry
    (sku : Sku) (currency : Currency) (unitCost retailUnitPrice wholesaleUnitPrice : Money)
    (retailMargin wholesaleMargin : Money) (wholesaleMinQty : Quantity) :
    Except ValidationError TradePriceBookEntry :=
  if hRetail : unitCost + retailMargin ≤ retailUnitPrice then
    if hWholesale : unitCost + wholesaleMargin ≤ wholesaleUnitPrice then
      if hPrice : wholesaleUnitPrice ≤ retailUnitPrice then
        if hMinQty : 0 < wholesaleMinQty then
          Except.ok
            { sku := sku
              currency := currency
              unitCost := unitCost
              retailUnitPrice := retailUnitPrice
              wholesaleUnitPrice := wholesaleUnitPrice
              retailMargin := retailMargin
              wholesaleMargin := wholesaleMargin
              wholesaleMinQty := wholesaleMinQty
              retail_margin_ok := hRetail
              wholesale_margin_ok := hWholesale
              wholesalePrice_le_retailPrice := hPrice
              wholesaleMinQty_pos := hMinQty }
        else
          Except.error ValidationError.b2bInvariantFailed
      else
        Except.error ValidationError.b2bInvariantFailed
    else
      Except.error ValidationError.b2bInvariantFailed
  else
    Except.error ValidationError.b2bInvariantFailed

/-- Validate a retail line discount against retail gross. -/
def validateRetailLine
    (entry : TradePriceBookEntry) (quantity : Quantity) (discount : Money) :
    Except ValidationError RetailLine :=
  if hDiscount : discount ≤ entry.retailUnitPrice * quantity then
    Except.ok
      { entry := entry
        quantity := quantity
        discount := discount
        discount_le_gross := hDiscount }
  else
    Except.error ValidationError.b2bInvariantFailed

/-- Validate a wholesale line against minimum quantity and discount bounds. -/
def validateWholesaleLine
    (entry : TradePriceBookEntry) (quantity : Quantity) (discount : Money) :
    Except ValidationError WholesaleLine :=
  if hQty : entry.wholesaleMinQty ≤ quantity then
    if hDiscount : discount ≤ entry.wholesaleUnitPrice * quantity then
      Except.ok
        { entry := entry
          quantity := quantity
          minQty_ok := hQty
          discount := discount
          discount_le_gross := hDiscount }
    else
      Except.error ValidationError.b2bInvariantFailed
  else
    Except.error ValidationError.b2bInvariantFailed

/-- Validate a wholesale credit account against eligibility and outstanding balance. -/
def validateWholesaleCreditAccount
    (customer : Customer) (creditLimit outstanding : Money) :
    Except ValidationError WholesaleCreditAccount :=
  if hCustomer : customerCanBuyWholesale customer then
    if hOutstanding : outstanding ≤ creditLimit then
      Except.ok
        { customer := customer
          creditLimit := creditLimit
          outstanding := outstanding
          customer_can_buy_wholesale := hCustomer
          outstanding_le_limit := hOutstanding }
    else
      Except.error ValidationError.b2bInvariantFailed
  else
    Except.error ValidationError.b2bInvariantFailed

/-! ### Dropshipping and dropship-profit validators -/

/-- Validate daily supplier capacity against accepted count and supplier maximum. -/
def validateSupplierDailyCapacity
    (supplier : DropshipSupplier) (dailyOrderCapacity ordersAcceptedToday : Nat) :
    Except ValidationError SupplierDailyCapacity :=
  if hAccepted : ordersAcceptedToday ≤ dailyOrderCapacity then
    if hCapacity : dailyOrderCapacity ≤ supplier.maxDailyOrders then
      Except.ok
        { supplier := supplier
          dailyOrderCapacity := dailyOrderCapacity
          ordersAcceptedToday := ordersAcceptedToday
          accepted_le_capacity := hAccepted
          capacity_le_supplier_max := hCapacity }
    else
      Except.error ValidationError.dropshippingInvariantFailed
  else
    Except.error ValidationError.dropshippingInvariantFailed

/-- Validate dropship offer cost and currency invariants. -/
def validateDropshipOffer
    (sku : Sku) (supplier : DropshipSupplier) (supplierUnitCost saleUnitPrice : Money)
    (unitWeight : Weight) (availableQty : Quantity) (currency : Currency)
    (active : Bool) :
    Except ValidationError DropshipOffer :=
  if hCost : supplierUnitCost ≤ saleUnitPrice then
    if hCurrency : currency = supplier.currency then
      Except.ok
        { sku := sku
          supplier := supplier
          supplierUnitCost := supplierUnitCost
          saleUnitPrice := saleUnitPrice
          unitWeight := unitWeight
          availableQty := availableQty
          currency := currency
          active := active
          supplierCost_le_salePrice := hCost
          currency_matches_supplier := hCurrency }
    else
      Except.error ValidationError.dropshippingInvariantFailed
  else
    Except.error ValidationError.dropshippingInvariantFailed

/-- Validate a supplier reservation against supplier identity and available quantity. -/
def validateSupplierReservation
    (offer : DropshipOffer) (supplier : DropshipSupplier) (quantity : Quantity)
    (status : SupplierReservationStatus) :
    Except ValidationError SupplierReservation :=
  if hSupplier : offer.supplier.id = supplier.id then
    if hQuantity : quantity ≤ offer.availableQty then
      Except.ok
        { offer := offer
          supplier := supplier
          quantity := quantity
          status := status
          same_supplier := hSupplier
          quantity_le_available := hQuantity }
    else
      Except.error ValidationError.dropshippingInvariantFailed
  else
    Except.error ValidationError.dropshippingInvariantFailed

/-- Validate a dropship order line against supplier, stock, discount, and margin checks. -/
def validateDropshipLine
    (offer : DropshipOffer) (quantity : Quantity) (discount : Money) :
    Except ValidationError DropshipLine :=
  if hSupplier : supplierCanReceiveOrders offer.supplier then
    if hActive : offer.active = true then
      if hQuantity : quantity ≤ offer.availableQty then
        if hDiscount : discount ≤ offer.saleUnitPrice * quantity then
          if hMargin :
              offer.supplierUnitCost * quantity + discount ≤
                offer.saleUnitPrice * quantity then
            Except.ok
              { offer := offer
                quantity := quantity
                discount := discount
                supplier_can_receive_orders := hSupplier
                offer_active := hActive
                quantity_le_supplier_available := hQuantity
                discount_le_saleGross := hDiscount
                margin_after_discount_ok := hMargin }
          else
            Except.error ValidationError.dropshippingInvariantFailed
        else
          Except.error ValidationError.dropshippingInvariantFailed
      else
        Except.error ValidationError.dropshippingInvariantFailed
    else
      Except.error ValidationError.dropshippingInvariantFailed
  else
    Except.error ValidationError.dropshippingInvariantFailed

/-- Validate and normalize a reserved dropship line with a confirmed reservation. -/
def validateReservedDropshipLine
    (line : DropshipLine) (supplier : DropshipSupplier) :
    Except ValidationError ReservedDropshipLine :=
  if hSupplier : line.offer.supplier.id = supplier.id then
    if hQuantity : line.quantity ≤ line.offer.availableQty then
      let reservation : SupplierReservation :=
        { offer := line.offer
          supplier := supplier
          quantity := line.quantity
          status := SupplierReservationStatus.Confirmed
          same_supplier := hSupplier
          quantity_le_available := hQuantity }
      Except.ok
        { line := line
          reservation := reservation
          same_offer := rfl
          same_quantity := rfl
          confirmed := rfl }
    else
      Except.error ValidationError.dropshippingInvariantFailed
  else
    Except.error ValidationError.dropshippingInvariantFailed

/-- Validate a supplier purchase order against quote supplier, weight, and total. -/
def validateDropshipPurchaseOrder
    (supplier : DropshipSupplier) (lines : List DropshipLine)
    (quote : DropshipShippingQuote) (status : DropshipPOStatus)
    (total : Money) :
    Except ValidationError DropshipPurchaseOrder :=
  if hSupplier : quote.supplierId = supplier.id then
    if hWeight : dropshipWeightTotal lines ≤ quote.maxWeight then
      if hTotal : total = dropshipSupplierCostTotal lines + quote.price then
        Except.ok
          { supplier := supplier
            lines := lines
            quote := quote
            status := status
            total := total
            quote_supplier_matches := hSupplier
            weight_ok := hWeight
            total_correct := hTotal }
      else
        Except.error ValidationError.dropshippingInvariantFailed
    else
      Except.error ValidationError.dropshippingInvariantFailed
  else
    Except.error ValidationError.dropshippingInvariantFailed

/-- Validate dropship fulfillment revenue against the customer order. -/
def validateDropshipFulfillment
    (customerOrder : Order) (purchaseOrder : DropshipPurchaseOrder)
    (segmentRevenue : Money) :
    Except ValidationError DropshipFulfillment :=
  if hRevenue : segmentRevenue = dropshipSaleNetTotal purchaseOrder.lines then
    if hLeOrder : segmentRevenue ≤ customerOrder.total then
      Except.ok
        { customerOrder := customerOrder
          purchaseOrder := purchaseOrder
          segmentRevenue := segmentRevenue
          segmentRevenue_correct := hRevenue
          segmentRevenue_le_order_total := hLeOrder }
    else
      Except.error ValidationError.dropshippingInvariantFailed
  else
    Except.error ValidationError.dropshippingInvariantFailed

/-- Validate a dropship return request against sold quantity and cost/refund caps. -/
def validateDropshipReturnRequest
    (line : DropshipLine) (returnQty : Quantity)
    (customerRefund supplierCredit : Money) :
    Except ValidationError DropshipReturnRequest :=
  if hAccepts : line.offer.supplier.acceptsReturns = true then
    if hQty : returnQty ≤ line.quantity then
      if hRefund : customerRefund ≤ dropshipLineCustomerNet line then
        if hCredit : supplierCredit ≤ dropshipLineSupplierCost line then
          Except.ok
            { line := line
              returnQty := returnQty
              customerRefund := customerRefund
              supplierCredit := supplierCredit
              supplier_accepts_returns := hAccepts
              returnQty_le_soldQty := hQty
              refund_le_customerNet := hRefund
              supplierCredit_le_supplierCost := hCredit }
        else
          Except.error ValidationError.dropshippingInvariantFailed
      else
        Except.error ValidationError.dropshippingInvariantFailed
    else
      Except.error ValidationError.dropshippingInvariantFailed
  else
    Except.error ValidationError.dropshippingInvariantFailed

/-- Validate a guaranteed profit quote. -/
def validateGuaranteedDropshipProfitQuote
    (revenue : Money) (costs : DropshipProfitCosts) (minProfit profit : Money)
    (signedProfit : SignedMoney) :
    Except ValidationError GuaranteedDropshipProfitQuote :=
  if hProfit : profit = profitAmount revenue (dropshipProfitCostsTotal costs) then
    if hSigned :
        signedProfit = profitLossAmount revenue (dropshipProfitCostsTotal costs) then
      if hMin : dropshipProfitCostsTotal costs + minProfit ≤ revenue then
        Except.ok
          { revenue := revenue
            costs := costs
            minProfit := minProfit
            profit := profit
            signedProfit := signedProfit
            profit_correct := hProfit
            signed_profit_correct := hSigned
            costs_plus_minProfit_le_revenue := hMin }
      else
        Except.error ValidationError.profitInvariantFailed
    else
      Except.error ValidationError.profitInvariantFailed
  else
    Except.error ValidationError.profitInvariantFailed

/-- Validate component-wise upper bounds for dropship costs. -/
def validateDropshipCostUpperBounds
    (actual upper : DropshipProfitCosts) :
    Except ValidationError DropshipCostUpperBounds :=
  if hGoods : actual.supplierGoods ≤ upper.supplierGoods then
    if hShipping : actual.supplierShipping ≤ upper.supplierShipping then
      if hMarketplace : actual.marketplaceFee ≤ upper.marketplaceFee then
        if hPayment : actual.paymentFee ≤ upper.paymentFee then
          if hAd : actual.adSpend ≤ upper.adSpend then
            if hReturn : actual.returnReserve ≤ upper.returnReserve then
              if hTax : actual.tax ≤ upper.tax then
                if hOther : actual.otherCosts ≤ upper.otherCosts then
                  Except.ok
                    { actual := actual
                      upper := upper
                      supplierGoods_le := hGoods
                      supplierShipping_le := hShipping
                      marketplaceFee_le := hMarketplace
                      paymentFee_le := hPayment
                      adSpend_le := hAd
                      returnReserve_le := hReturn
                      tax_le := hTax
                      otherCosts_le := hOther }
                else
                  Except.error ValidationError.profitInvariantFailed
              else
                Except.error ValidationError.profitInvariantFailed
            else
              Except.error ValidationError.profitInvariantFailed
          else
            Except.error ValidationError.profitInvariantFailed
        else
          Except.error ValidationError.profitInvariantFailed
      else
        Except.error ValidationError.profitInvariantFailed
    else
      Except.error ValidationError.profitInvariantFailed
  else
    Except.error ValidationError.profitInvariantFailed

/-! ### Competitor, merchandising, fulfillment-finance, and post-purchase validators -/

/-- Validate a singleton competitor benchmark from its best offer. -/
def validateSingletonCompetitorPriceBenchmark
    (sku : Sku) (currency : Currency) (bestOffer : CompetitorOffer) :
    Except ValidationError CompetitorPriceBenchmark :=
  if hRelevant : competitorOfferRelevant bestOffer sku currency then
    Except.ok
      { sku := sku
        currency := currency
        offers := [bestOffer]
        bestOffer := bestOffer
        bestOffer_in_offers := by simp
        bestOffer_relevant := hRelevant
        bestOffer_is_lowest := by
          intro other hmem _hrel
          simp at hmem
          cases hmem
          exact Nat.le_refl bestOffer.price }
  else
    Except.error ValidationError.competitorInvariantFailed

/-- Validate a competitor-aware dropship offer against benchmark, profit, and price checks. -/
def validateCompetitorAwareDropshipOffer
    (offer : DropshipOffer) (benchmark : CompetitorPriceBenchmark)
    (discount : Money) (costs : DropshipProfitCosts) (minProfit : Money) :
    Except ValidationError CompetitorAwareDropshipOffer :=
  if hSku : benchmark.sku = offer.sku then
    if hCurrency : benchmark.currency = offer.currency then
      if hProfit : priceProfitableForMinProfit offer.saleUnitPrice discount costs minProfit then
        if hPrice : offer.saleUnitPrice ≤ benchmark.bestOffer.price then
          Except.ok
            { offer := offer
              benchmark := benchmark
              discount := discount
              costs := costs
              minProfit := minProfit
              same_sku := hSku
              same_currency := hCurrency
              salePrice_profitable := hProfit
              salePrice_le_bestCompetitor := hPrice }
        else
          Except.error ValidationError.competitorInvariantFailed
      else
        Except.error ValidationError.competitorInvariantFailed
    else
      Except.error ValidationError.competitorInvariantFailed
  else
    Except.error ValidationError.competitorInvariantFailed

/-- Validate a brand pricing policy by checking MAP does not exceed MSRP. -/
def validateBrandPricingPolicy (mapPrice msrp : Money) :
    Except ValidationError BrandPricingPolicy :=
  if hMap : mapPrice ≤ msrp then
    Except.ok { mapPrice := mapPrice, msrp := msrp, map_le_msrp := hMap }
  else
    Except.error ValidationError.merchandisingInvariantFailed

/-- Validate that a bundle component has a positive per-bundle quantity. -/
def validateBundleComponent
    (sku : Sku) (unitsPerBundle stockAvailable : Quantity) :
    Except ValidationError BundleComponent :=
  if hUnits : 0 < unitsPerBundle then
    Except.ok
      { sku := sku
        unitsPerBundle := unitsPerBundle
        stockAvailable := stockAvailable
        units_pos := hUnits }
  else
    Except.error ValidationError.merchandisingInvariantFailed

/-- Recursive executable check that every bundle component can satisfy a bundle quantity. -/
def bundleComponentsCanFulfillAll
    (bundleQty : Quantity) : List BundleComponent → Prop
  | [] => True
  | component :: rest =>
      componentCanFulfillBundles bundleQty component ∧
        bundleComponentsCanFulfillAll bundleQty rest

/-- The recursive bundle check implies the existing membership-based invariant. -/
theorem bundleComponentsCanFulfillAll_sound
    {bundleQty : Quantity} :
    ∀ {components : List BundleComponent},
    bundleComponentsCanFulfillAll bundleQty components →
    ∀ c ∈ components, componentCanFulfillBundles bundleQty c := by
  intro components
  induction components with
  | nil =>
      intro _h c hmem
      cases hmem
  | cons head rest ih =>
      intro h c hmem
      cases hmem with
      | head =>
          exact h.left
      | tail _ htail =>
          exact ih h.right c htail

/-- Validate a bundle reservation by scanning every component for stock sufficiency. -/
def validateBundleReservation
    (bundleQty : Quantity) (components : List BundleComponent) :
    Except ValidationError BundleReservation :=
  if hAll : bundleComponentsCanFulfillAll bundleQty components then
    Except.ok
      { bundleQty := bundleQty
        components := components
        all_components_safe := bundleComponentsCanFulfillAll_sound hAll }
  else
    Except.error ValidationError.merchandisingInvariantFailed

/-- Validate an accepted promotion set against discount cap and profit floor. -/
def validateAcceptedPromotionSet
    (resultingPrice totalDiscount discountCap profitFloor : Money) :
    Except ValidationError AcceptedPromotionSet :=
  if hDiscount : totalDiscount ≤ discountCap then
    if hFloor : profitFloor ≤ resultingPrice then
      Except.ok
        { resultingPrice := resultingPrice
          totalDiscount := totalDiscount
          discountCap := discountCap
          profitFloor := profitFloor
          discount_le_cap := hDiscount
          floor_le_price := hFloor }
    else
      Except.error ValidationError.merchandisingInvariantFailed
  else
    Except.error ValidationError.merchandisingInvariantFailed

/-- Validate search results against archive, stock, and margin flags. -/
def validateSearchResultItem (item : SearchResultItem) :
    Except ValidationError ValidSearchResultItem :=
  if hArchived : item.archived = false then
    if hStock : item.inStock = true then
      if hMargin : item.marginSafe = true then
        Except.ok
          { item := item
            not_archived := hArchived
            sellable := hStock
            margin_safe := hMargin }
      else
        Except.error ValidationError.merchandisingInvariantFailed
    else
      Except.error ValidationError.merchandisingInvariantFailed
  else
    Except.error ValidationError.merchandisingInvariantFailed

/-- Validate an FX exchange rate by checking its denominator. -/
def validateExchangeRate
    (source target : Currency) (numerator denominator : Nat)
    (observedAt : Timestamp) :
    Except ValidationError ExchangeRate :=
  if hDenominator : 0 < denominator then
    Except.ok
      { source := source
        target := target
        numerator := numerator
        denominator := denominator
        denominator_pos := hDenominator
        observedAt := observedAt }
  else
    Except.error ValidationError.financeInvariantFailed

/-- Validate tax arithmetic with the declared rounding mode. -/
def validateTaxCalculation
    (taxableAmount : Money) (rate : TaxRate) (roundingMode : RoundingMode)
    (tax total : Money) :
    Except ValidationError TaxCalculation :=
  if hTax : tax = taxAmountRounded roundingMode rate taxableAmount then
    if hTotal : total = taxableAmount + tax then
      Except.ok
        { taxableAmount := taxableAmount
          rate := rate
          roundingMode := roundingMode
          tax := tax
          total := total
          tax_correct := hTax
          total_correct := hTotal }
    else
      Except.error ValidationError.financeInvariantFailed
  else
    Except.error ValidationError.financeInvariantFailed

/-- Validate a tax-inclusive price decomposition. -/
def validateTaxInclusivePrice (gross net tax : Money) :
    Except ValidationError TaxInclusivePrice :=
  if hGross : gross = net + tax then
    Except.ok
      { gross := gross
        net := net
        tax := tax
        gross_correct := hGross }
  else
    Except.error ValidationError.taxInvariantFailed

/-- Successful tax-inclusive price validation conserves net and tax. -/
theorem validateTaxInclusivePrice_sound
    {price : TaxInclusivePrice}
    (_h :
      validateTaxInclusivePrice price.gross price.net price.tax =
        Except.ok price) :
    price.net + price.tax = price.gross := by
  exact taxInclusivePrice_conserves_components price

/-- Validate a tax-exclusive price decomposition. -/
def validateTaxExclusivePrice (net tax total : Money) :
    Except ValidationError TaxExclusivePrice :=
  if hTotal : total = net + tax then
    Except.ok
      { net := net
        tax := tax
        total := total
        total_correct := hTotal }
  else
    Except.error ValidationError.taxInvariantFailed

/-- Successful tax-exclusive price validation conserves net and tax. -/
theorem validateTaxExclusivePrice_sound
    {price : TaxExclusivePrice}
    (_h :
      validateTaxExclusivePrice price.net price.tax price.total =
        Except.ok price) :
    price.net + price.tax = price.total := by
  exact taxExclusivePrice_conserves_components price

/-- Raw tax invoice line before arithmetic and treatment checks. -/
structure RawTaxInvoiceLine where
  sku : Sku
  quantity : Quantity
  unitPrice : Money
  discount : Money
  treatment : TaxTreatment
  rate : TaxRate
  roundingMode : RoundingMode
  taxableAmount : Money
  tax : Money
  total : Money

/-- Validate a tax invoice line with discount, taxable amount, tax, and total checks. -/
def validateTaxInvoiceLine (raw : RawTaxInvoiceLine) :
    Except ValidationError TaxInvoiceLine :=
  if hDiscount : raw.discount ≤ raw.unitPrice * raw.quantity then
    if hTaxable : raw.taxableAmount = raw.unitPrice * raw.quantity - raw.discount then
      if hTax :
          raw.tax =
            taxForTreatment raw.treatment raw.roundingMode raw.rate raw.taxableAmount then
        if hTotal : raw.total = raw.taxableAmount + raw.tax then
          Except.ok
            { sku := raw.sku
              quantity := raw.quantity
              unitPrice := raw.unitPrice
              discount := raw.discount
              treatment := raw.treatment
              rate := raw.rate
              roundingMode := raw.roundingMode
              taxableAmount := raw.taxableAmount
              tax := raw.tax
              total := raw.total
              discount_le_gross := hDiscount
              taxableAmount_correct := hTaxable
              tax_correct := hTax
              total_correct := hTotal }
        else
          Except.error ValidationError.taxInvariantFailed
      else
        Except.error ValidationError.taxInvariantFailed
    else
      Except.error ValidationError.taxInvariantFailed
  else
    Except.error ValidationError.taxInvariantFailed

/-- Successful tax-invoice-line validation proves tax arithmetic and conservation. -/
theorem validateTaxInvoiceLine_sound
    {raw : RawTaxInvoiceLine} {line : TaxInvoiceLine}
    (_h : validateTaxInvoiceLine raw = Except.ok line) :
    line.discount ≤ line.unitPrice * line.quantity ∧
      line.taxableAmount = line.unitPrice * line.quantity - line.discount ∧
      line.tax = taxForTreatment line.treatment line.roundingMode
        line.rate line.taxableAmount ∧
      line.taxableAmount + line.tax = line.total := by
  exact ⟨line.discount_le_gross, line.taxableAmount_correct,
    line.tax_correct, taxInvoiceLine_total_conserves_components line⟩

/-- Validate tax invoice lines in order, stopping at the first failed line. -/
def validateTaxInvoiceLines :
    List RawTaxInvoiceLine → Except ValidationError (List TaxInvoiceLine)
  | [] => Except.ok []
  | raw :: rest => do
      let line ← validateTaxInvoiceLine raw
      let lines ← validateTaxInvoiceLines rest
      Except.ok (line :: lines)

/-- Raw tax invoice before line and component totals have been checked. -/
structure RawTaxInvoice where
  id : Id
  issuedAt : Timestamp
  sellerId : Id
  buyerId : CustomerId
  jurisdiction : TaxJurisdiction
  currency : Currency
  lines : List RawTaxInvoiceLine
  subtotal : Money
  tax : Money
  shipping : Money
  discount : Money
  total : Money

/-- Validate a tax invoice against line totals and component conservation. -/
def validateTaxInvoice (raw : RawTaxInvoice) :
    Except ValidationError TaxInvoice := do
  let lines ← validateTaxInvoiceLines raw.lines
  if hSubtotal : raw.subtotal = invoiceLineSubtotalTotal lines then
    if hTax : raw.tax = invoiceLineTaxTotal lines then
      if hDiscount : raw.discount ≤ raw.subtotal + raw.tax + raw.shipping then
        if hTotal : raw.total = raw.subtotal + raw.tax + raw.shipping - raw.discount then
          Except.ok
            { id := raw.id
              issuedAt := raw.issuedAt
              sellerId := raw.sellerId
              buyerId := raw.buyerId
              jurisdiction := raw.jurisdiction
              currency := raw.currency
              lines := lines
              subtotal := raw.subtotal
              tax := raw.tax
              shipping := raw.shipping
              discount := raw.discount
              total := raw.total
              subtotal_correct := hSubtotal
              tax_correct := hTax
              discount_le_components := hDiscount
              total_correct := hTotal }
        else
          Except.error ValidationError.taxInvariantFailed
      else
        Except.error ValidationError.taxInvariantFailed
    else
      Except.error ValidationError.taxInvariantFailed
  else
    Except.error ValidationError.taxInvariantFailed

/-- Successful tax-invoice validation proves line totals and component conservation. -/
theorem validateTaxInvoice_sound
    {raw : RawTaxInvoice} {invoice : TaxInvoice}
    (_h : validateTaxInvoice raw = Except.ok invoice) :
    invoice.subtotal = invoiceLineSubtotalTotal invoice.lines ∧
      invoice.tax = invoiceLineTaxTotal invoice.lines ∧
      invoice.total + invoice.discount =
        invoice.subtotal + invoice.tax + invoice.shipping := by
  exact ⟨taxInvoice_subtotal_matches_lines invoice,
    taxInvoice_tax_matches_lines invoice,
    invoice_total_add_discount_eq_components invoice⟩

/-- Validate an order-to-tax-invoice link against tax amount and currency. -/
def validateOrderTaxInvoiceLink (order : Order) (invoice : TaxInvoice) :
    Except ValidationError OrderTaxInvoiceLink :=
  if hTax : order.tax = invoice.tax then
    if hCurrency : invoice.currency = order.currency then
      Except.ok
        { order := order
          invoice := invoice
          order_tax_matches_invoice := hTax
          currency_matches := hCurrency }
    else
      Except.error ValidationError.taxInvariantFailed
  else
    Except.error ValidationError.taxInvariantFailed

/-- Successful order/tax-invoice link validation proves tax and currency agreement. -/
theorem validateOrderTaxInvoiceLink_sound
    {link : OrderTaxInvoiceLink}
    (_h :
      validateOrderTaxInvoiceLink link.order link.invoice = Except.ok link) :
    link.order.tax = link.invoice.tax ∧
      link.invoice.currency = link.order.currency := by
  exact ⟨orderTaxInvoiceLink_tax_matches link,
    orderTaxInvoiceLink_currency_matches link⟩

/-- Validate a B2B tax exemption certificate validity window. -/
def validateTaxExemptionCertificate
    (customerId : CustomerId) (jurisdictionId : Id)
    (validFrom validUntil : Timestamp) :
    Except ValidationError TaxExemptionCertificate :=
  if hWindow : validFrom ≤ validUntil then
    Except.ok
      { customerId := customerId
        jurisdictionId := jurisdictionId
        validFrom := validFrom
        validUntil := validUntil
        valid_window := hWindow }
  else
    Except.error ValidationError.taxInvariantFailed

/-- Successful certificate validation exposes its ordered validity window. -/
theorem validateTaxExemptionCertificate_sound
    {certificate : TaxExemptionCertificate}
    (_h :
      validateTaxExemptionCertificate certificate.customerId
        certificate.jurisdictionId certificate.validFrom certificate.validUntil =
        Except.ok certificate) :
    certificate.validFrom ≤ certificate.validUntil := by
  exact certificate.valid_window

/-- Validate B2B tax exemption evidence for a customer and jurisdiction. -/
def validateB2BTaxExemption
    (customer : Customer) (jurisdiction : TaxJurisdiction)
    (certificate : TaxExemptionCertificate) (checkedAt : Timestamp) :
    Except ValidationError B2BTaxExemption :=
  if hCustomer : certificate.customerId = customer.id then
    if hJurisdiction : certificate.jurisdictionId = jurisdiction.id then
      if hWholesale : customer.wholesaleApproved = true then
        if hValid : certificateValidAt certificate checkedAt then
          Except.ok
            { customer := customer
              jurisdiction := jurisdiction
              certificate := certificate
              checkedAt := checkedAt
              customer_matches := hCustomer
              jurisdiction_matches := hJurisdiction
              wholesale_approved := hWholesale
              certificate_valid := hValid }
        else
          Except.error ValidationError.taxInvariantFailed
      else
        Except.error ValidationError.taxInvariantFailed
    else
      Except.error ValidationError.taxInvariantFailed
  else
    Except.error ValidationError.taxInvariantFailed

/-- Successful B2B exemption validation proves identity, approval, and validity. -/
theorem validateB2BTaxExemption_sound
    {exemption : B2BTaxExemption}
    (_h :
      validateB2BTaxExemption exemption.customer exemption.jurisdiction
        exemption.certificate exemption.checkedAt = Except.ok exemption) :
    exemption.certificate.customerId = exemption.customer.id ∧
      exemption.certificate.jurisdictionId = exemption.jurisdiction.id ∧
      exemption.customer.wholesaleApproved = true ∧
      exemption.checkedAt ≤ exemption.certificate.validUntil := by
  exact ⟨exemption.customer_matches, exemption.jurisdiction_matches,
    b2bTaxExemption_wholesale_approved exemption,
    b2bTaxExemption_certificate_not_expired exemption⟩

/-- Validate marketplace-facilitator tax collection evidence. -/
def validateMarketplaceFacilitatorTax
    (marketplace : Marketplace) (jurisdiction : TaxJurisdiction)
    (taxableAmount : Money) (rate : TaxRate) (roundingMode : RoundingMode)
    (tax : Money) (facilitatorCollects : Bool) (sellerTaxDue : Money) :
    Except ValidationError MarketplaceFacilitatorTax :=
  if hTax : tax = taxAmountRounded roundingMode rate taxableAmount then
    if hSellerDue :
        sellerTaxDue = sellerTaxDueForFacilitator facilitatorCollects tax then
      Except.ok
        { marketplace := marketplace
          jurisdiction := jurisdiction
          taxableAmount := taxableAmount
          rate := rate
          roundingMode := roundingMode
          tax := tax
          facilitatorCollects := facilitatorCollects
          sellerTaxDue := sellerTaxDue
          tax_correct := hTax
          sellerTaxDue_correct := hSellerDue }
    else
      Except.error ValidationError.taxInvariantFailed
  else
    Except.error ValidationError.taxInvariantFailed

/-- Successful facilitator-tax validation proves rounding and seller due. -/
theorem validateMarketplaceFacilitatorTax_sound
    {tax : MarketplaceFacilitatorTax}
    (_h :
      validateMarketplaceFacilitatorTax tax.marketplace tax.jurisdiction
        tax.taxableAmount tax.rate tax.roundingMode tax.tax
        tax.facilitatorCollects tax.sellerTaxDue = Except.ok tax) :
    tax.tax = taxAmountRounded tax.roundingMode tax.rate tax.taxableAmount ∧
      tax.sellerTaxDue =
        sellerTaxDueForFacilitator tax.facilitatorCollects tax.tax := by
  exact ⟨marketplaceFacilitatorTax_uses_declared_rounding tax,
    tax.sellerTaxDue_correct⟩

/-- Validate a carrier quote against package capacity and base cost. -/
def validateCarrierQuote
    (service : CarrierService) (package : Package) (price : Money) :
    Except ValidationError CarrierQuote :=
  if hWeight : package.weight ≤ service.maxWeight then
    if hPrice : service.baseCost ≤ price then
      Except.ok
        { service := service
          package := package
          price := price
          package_weight_ok := hWeight
          price_ge_cost := hPrice }
    else
      Except.error ValidationError.financeInvariantFailed
  else
    Except.error ValidationError.financeInvariantFailed

/-- Validate reconciliation tolerance against the expected/actual difference. -/
def validateReconciliationWithinTolerance
    (expected actual tolerance : Money) :
    Except ValidationError ReconciliationWithinTolerance :=
  if hDiff : absDiffNat expected actual ≤ tolerance then
    Except.ok
      { expected := expected
        actual := actual
        tolerance := tolerance
        diff_le_tolerance := hDiff }
  else
    Except.error ValidationError.financeInvariantFailed

/-- Validate a subscription plan by requiring a positive period. -/
def validateSubscriptionPlan (price : Money) (periodDays : Days) :
    Except ValidationError SubscriptionPlan :=
  if hPeriod : 0 < periodDays then
    Except.ok { price := price, periodDays := periodDays, period_pos := hPeriod }
  else
    Except.error ValidationError.postPurchaseInvariantFailed

/-- Validate recurring subscription billing chronology. -/
def validateRecurringSubscription
    (customer : CustomerId) (plan : SubscriptionPlan)
    (status : SubscriptionLifecycleStatus)
    (currentBillingDate nextBillingDate : Timestamp) :
    Except ValidationError RecurringSubscription :=
  if hNext : currentBillingDate < nextBillingDate then
    Except.ok
      { customer := customer
        plan := plan
        status := status
        currentBillingDate := currentBillingDate
        nextBillingDate := nextBillingDate
        next_after_current := hNext }
  else
    Except.error ValidationError.postPurchaseInvariantFailed

/-- Validate a gift-card redemption against card balance. -/
def validateGiftCardRedemption (card : GiftCard) (amount : Money) :
    Except ValidationError GiftCardRedemption :=
  if hAmount : amount ≤ card.balance then
    Except.ok { card := card, amount := amount, amount_le_balance := hAmount }
  else
    Except.error ValidationError.postPurchaseInvariantFailed

/-- Validate a chargeback against the original payment amount. -/
def validateChargeback (paymentAmount chargebackAmount : Money) :
    Except ValidationError Chargeback :=
  if hAmount : chargebackAmount ≤ paymentAmount then
    Except.ok
      { paymentAmount := paymentAmount
        chargebackAmount := chargebackAmount
        amount_le_payment := hAmount }
  else
    Except.error ValidationError.postPurchaseInvariantFailed

/-- Validate cashflow reserve safety from expected totals. -/
def validateCashflowPlan
    (startingCash requiredReserve expectedInflows expectedOutflows : Money) :
    Except ValidationError CashflowPlan :=
  if hReserve : requiredReserve + expectedOutflows ≤ startingCash + expectedInflows then
    Except.ok
      { startingCash := startingCash
        requiredReserve := requiredReserve
        expectedInflows := expectedInflows
        expectedOutflows := expectedOutflows
        reserve_safe := hReserve }
  else
    Except.error ValidationError.postPurchaseInvariantFailed

/-- Validate event-backed cashflow reserve safety. -/
def validateEventBackedCashflowPlan
    (startingCash requiredReserve : Money) (events : List CashflowEvent) :
    Except ValidationError EventBackedCashflowPlan :=
  if hReserve :
      requiredReserve + cashflowOutflowsTotal events ≤
        startingCash + cashflowInflowsTotal events then
    Except.ok
      { startingCash := startingCash
        requiredReserve := requiredReserve
        events := events
        reserve_safe := hReserve }
  else
    Except.error ValidationError.postPurchaseInvariantFailed

/-! ### Risk, event-sourcing, forecasting, and opportunity validators -/

/-- Validate an order-scoped audited command and construct its audit event. -/
def validateAuditedCommand
    (actor : Role) (action : Action) (orderId : OrderId) :
    Except ValidationError AuditedCommand :=
  if hAllowed : CanPerform actor action then
    Except.ok
      { actor := actor
        action := action
        orderId := orderId
        allowed := hAllowed
        event := { actor := actor, action := action, orderId := orderId }
        event_actor_matches := rfl
        event_action_matches := rfl
        event_order_matches := rfl }
  else
    Except.error ValidationError.auditPermissionDenied

/-- Validate an entity-scoped audited command and construct its audit event. -/
def validateAuditedEntityCommand
    (actor : Role) (action : Action) (subjectId : Id) :
    Except ValidationError AuditedEntityCommand :=
  if hAllowed : CanPerform actor action then
    Except.ok
      { actor := actor
        action := action
        subjectId := subjectId
        allowed := hAllowed
        event := { actor := actor, action := action, subjectId := subjectId }
        event_actor_matches := rfl
        event_action_matches := rfl
        event_subject_matches := rfl }
  else
    Except.error ValidationError.auditPermissionDenied

/-- Validate an event stream's ordering and stored cursor. -/
def validateEventStream (stream : EventStream) :
    Except ValidationError ValidEventStream :=
  if hStrict : streamSequencesStrictlyIncrease stream then
    if hCursor : stream.lastSequence = eventStreamComputedLastSequence stream then
      Except.ok
        { stream := stream
          sequences_strict := hStrict
          lastSequence_correct := hCursor }
    else
      Except.error ValidationError.eventStreamInvalid
  else
    Except.error ValidationError.eventStreamInvalid

/-- Successful event-stream validation exposes ordering and cursor correctness. -/
theorem validateEventStream_sound
    {stream : EventStream} {valid : ValidEventStream}
    (_h : validateEventStream stream = Except.ok valid) :
    streamSequencesStrictlyIncrease valid.stream ∧
      valid.stream.lastSequence = eventStreamComputedLastSequence valid.stream := by
  exact ⟨valid.sequences_strict, valid.lastSequence_correct⟩

/-- Validate supplier quality metrics against a risk policy. -/
def validateApprovedSupplierQuality
    (supplier : DropshipSupplier) (metrics : SupplierQualityMetrics)
    (policy : SupplierRiskPolicy) :
    Except ValidationError ApprovedSupplierQuality :=
  if hDefect : metrics.defectRateBps ≤ policy.maxDefectRateBps then
    if hLate : metrics.lateShipmentRateBps ≤ policy.maxLateShipmentRateBps then
      if hCancellation :
          metrics.cancellationRateBps ≤ policy.maxCancellationRateBps then
        Except.ok
          { supplier := supplier
            metrics := metrics
            policy := policy
            defect_ok := hDefect
            late_ok := hLate
            cancellation_ok := hCancellation }
      else
        Except.error ValidationError.supplierQualityInvalid
    else
      Except.error ValidationError.supplierQualityInvalid
  else
    Except.error ValidationError.supplierQualityInvalid

/-- Validate a dropship opportunity candidate. -/
def validateDropshipOpportunityCandidate
    (sku : Sku) (units : Quantity) (targetPrice requiredCapital expectedProfit : Money)
    (minProfit competitorPrice : Money) (costs : DropshipProfitCosts) :
    Except ValidationError DropshipOpportunityCandidate :=
  if hCapital : 0 < requiredCapital then
    if hProfit : minProfit ≤ expectedProfit then
      if hPrice : priceProfitableForMinProfit targetPrice 0 costs minProfit then
        if hCompetitive : targetPrice ≤ competitorPrice then
          Except.ok
            { sku := sku
              units := units
              targetPrice := targetPrice
              requiredCapital := requiredCapital
              expectedProfit := expectedProfit
              minProfit := minProfit
              competitorPrice := competitorPrice
              costs := costs
              capital_pos := hCapital
              expectedProfit_ge_minProfit := hProfit
              price_profitable := hPrice
              targetPrice_le_competitor := hCompetitive }
        else
          Except.error ValidationError.opportunityInvariantFailed
      else
        Except.error ValidationError.opportunityInvariantFailed
    else
      Except.error ValidationError.opportunityInvariantFailed
  else
    Except.error ValidationError.opportunityInvariantFailed

/-- Validate selected opportunity capital against the investment fund. -/
def validateDropshipOpportunityPortfolio
    (selected : List DropshipOpportunityCandidate) (investmentFund : Money) :
    Except ValidationError DropshipOpportunityPortfolio :=
  if hCapital : candidatesCapitalTotal selected ≤ investmentFund then
    Except.ok
      { selected := selected
        investmentFund := investmentFund
        capital_le_fund := hCapital }
  else
    Except.error ValidationError.opportunityInvariantFailed

/-! ### CRM validators -/

/-- Validate CRM account value safety. -/
def validateCRMAccount
    (id : AccountId) (customer : Customer) (tier : AccountTier)
    (status : CRMAccountStatus) (lifetimeValue openBalance : Money) :
    Except ValidationError CRMAccount :=
  if hBalance : openBalance ≤ lifetimeValue then
    Except.ok
      { id := id
        customer := customer
        tier := tier
        status := status
        lifetimeValue := lifetimeValue
        openBalance := openBalance
        openBalance_le_lifetimeValue := hBalance }
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate that a CRM account is active. -/
def validateActiveCRMAccount (account : CRMAccount) :
    Except ValidationError ActiveCRMAccount :=
  if hActive : crmAccountActive account then
    Except.ok { account := account, active := hActive }
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate CRM account/contact identity links. -/
def validateCRMAccountContact
    (account : CRMAccount) (contact : CRMContact) :
    Except ValidationError CRMAccountContact :=
  if hAccount : contact.accountId = account.id then
    if hCustomer : contact.customerId = account.customer.id then
      Except.ok
        { account := account
          contact := contact
          contact_account_matches := hAccount
          contact_customer_matches := hCustomer }
    else
      Except.error ValidationError.crmInvariantFailed
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate a permitted customer marketing message. -/
def validatePermittedCustomerMessage
    (interactionId : InteractionId) (contact : CRMContact) (sentAt : Timestamp) :
    Except ValidationError PermittedCustomerMessage :=
  if hPermitted : contactCanReceiveMarketing contact then
    Except.ok
      { interactionId := interactionId
        contact := contact
        sentAt := sentAt
        permitted := hPermitted }
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate and normalize a permitted message for an account/contact pair. -/
def validatePermittedAccountMessage
    (accountContact : CRMAccountContact)
    (interactionId : InteractionId) (sentAt : Timestamp) :
    Except ValidationError PermittedAccountMessage :=
  if hPermitted : contactCanReceiveMarketing accountContact.contact then
    let message : PermittedCustomerMessage :=
      { interactionId := interactionId
        contact := accountContact.contact
        sentAt := sentAt
        permitted := hPermitted }
    Except.ok
      { accountContact := accountContact
        message := message
        message_contact_matches := rfl }
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate CRM interaction chronology. -/
def validateCRMInteraction
    (id : InteractionId) (accountId : AccountId) (contactId : ContactId)
    (kind : InteractionKind) (occurredAt followUpDueAt : Timestamp) :
    Except ValidationError CRMInteraction :=
  if hFollowUp : occurredAt ≤ followUpDueAt then
    Except.ok
      { id := id
        accountId := accountId
        contactId := contactId
        kind := kind
        occurredAt := occurredAt
        followUpDueAt := followUpDueAt
        followUp_after_occurrence := hFollowUp }
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate CRM interaction identity against an account/contact pair. -/
def validateCRMInteractionForContact
    (accountContact : CRMAccountContact) (interaction : CRMInteraction) :
    Except ValidationError CRMInteractionForContact :=
  if hAccount : interaction.accountId = accountContact.account.id then
    if hContact : interaction.contactId = accountContact.contact.id then
      Except.ok
        { accountContact := accountContact
          interaction := interaction
          interaction_account_matches := hAccount
          interaction_contact_matches := hContact }
    else
      Except.error ValidationError.crmInvariantFailed
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate lead timestamp ordering. -/
def validateLead
    (id : LeadId) (accountId : AccountId) (contactId : ContactId)
    (sourceCampaign : Option CampaignId) (status : LeadStatus)
    (estimatedValue : Money) (currency : Currency)
    (createdAt updatedAt : Timestamp) :
    Except ValidationError Lead :=
  if hUpdated : createdAt ≤ updatedAt then
    Except.ok
      { id := id
        accountId := accountId
        contactId := contactId
        sourceCampaign := sourceCampaign
        status := status
        estimatedValue := estimatedValue
        currency := currency
        createdAt := createdAt
        updatedAt := updatedAt
        created_le_updated := hUpdated }
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate lead identity against an account/contact pair. -/
def validateLeadForContact
    (accountContact : CRMAccountContact) (lead : Lead) :
    Except ValidationError LeadForContact :=
  if hAccount : lead.accountId = accountContact.account.id then
    if hContact : lead.contactId = accountContact.contact.id then
      Except.ok
        { accountContact := accountContact
          lead := lead
          lead_account_matches := hAccount
          lead_contact_matches := hContact }
    else
      Except.error ValidationError.crmInvariantFailed
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate a sales opportunity's timestamps and stage probability. -/
def validateSalesOpportunity
    (id : OpportunityId) (accountId : AccountId) (contactId : ContactId)
    (sourceLead : Option LeadId) (stage : OpportunityStage)
    (amount : Money) (currency : Currency) (probability : BasisPoints)
    (openedAt updatedAt expectedCloseAt : Timestamp) :
    Except ValidationError SalesOpportunity :=
  if hUpdated : openedAt ≤ updatedAt then
    if hExpected : openedAt ≤ expectedCloseAt then
      if hProbability : opportunityStageProbabilityAllowed stage probability then
        Except.ok
          { id := id
            accountId := accountId
            contactId := contactId
            sourceLead := sourceLead
            stage := stage
            amount := amount
            currency := currency
            probability := probability
            openedAt := openedAt
            updatedAt := updatedAt
            expectedCloseAt := expectedCloseAt
            opened_le_updated := hUpdated
            opened_le_expectedClose := hExpected
            probability_matches_stage := hProbability }
      else
        Except.error ValidationError.crmInvariantFailed
    else
      Except.error ValidationError.crmInvariantFailed
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate opportunity identity against an account/contact pair. -/
def validateOpportunityForContact
    (accountContact : CRMAccountContact) (opportunity : SalesOpportunity) :
    Except ValidationError OpportunityForContact :=
  if hAccount : opportunity.accountId = accountContact.account.id then
    if hContact : opportunity.contactId = accountContact.contact.id then
      Except.ok
        { accountContact := accountContact
          opportunity := opportunity
          opportunity_account_matches := hAccount
          opportunity_contact_matches := hContact }
    else
      Except.error ValidationError.crmInvariantFailed
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate that a sales pipeline is currency-consistent. -/
def validateSalesPipeline
    (currency : Currency) (opportunities : List SalesOpportunity) :
    Except ValidationError SalesPipeline :=
  if hCurrency : opportunitiesUseCurrency currency opportunities then
    Except.ok
      { currency := currency
        opportunities := opportunities
        currency_consistent := hCurrency }
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate retention segment discount cap. -/
def validateCustomerSegment
    (id : SegmentId) (name : String) (memberCount : Nat)
    (minLifetimeValue maxRetentionDiscount : Money) :
    Except ValidationError CustomerSegment :=
  if hDiscount : maxRetentionDiscount ≤ minLifetimeValue then
    Except.ok
      { id := id
        name := name
        memberCount := memberCount
        minLifetimeValue := minLifetimeValue
        maxRetentionDiscount := maxRetentionDiscount
        discount_le_min_lifetime_value := hDiscount }
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate that an account meets a segment value floor. -/
def validateSegmentMembership
    (account : CRMAccount) (segment : CustomerSegment) :
    Except ValidationError SegmentMembership :=
  if hFloor : segment.minLifetimeValue ≤ account.lifetimeValue then
    Except.ok
      { account := account
        segment := segment
        account_meets_value_floor := hFloor }
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate support case chronology. -/
def validateSupportCase
    (id : SupportCaseId) (accountId : AccountId) (contactId : ContactId)
    (orderId : Option OrderId) (status : SupportCaseStatus)
    (priority : SupportPriority)
    (openedAt lastUpdatedAt slaDueAt : Timestamp) :
    Except ValidationError SupportCase :=
  if hUpdated : openedAt ≤ lastUpdatedAt then
    if hSla : openedAt ≤ slaDueAt then
      Except.ok
        { id := id
          accountId := accountId
          contactId := contactId
          orderId := orderId
          status := status
          priority := priority
          openedAt := openedAt
          lastUpdatedAt := lastUpdatedAt
          slaDueAt := slaDueAt
          opened_le_lastUpdated := hUpdated
          opened_le_slaDue := hSla }
    else
      Except.error ValidationError.crmInvariantFailed
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate support case identity against an account/contact pair. -/
def validateSupportCaseForContact
    (accountContact : CRMAccountContact) (case_ : SupportCase) :
    Except ValidationError SupportCaseForContact :=
  if hAccount : case_.accountId = accountContact.account.id then
    if hContact : case_.contactId = accountContact.contact.id then
      Except.ok
        { accountContact := accountContact
          case_ := case_
          case_account_matches := hAccount
          case_contact_matches := hContact }
    else
      Except.error ValidationError.crmInvariantFailed
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate resolved support case status, chronology, and SLA. -/
def validateResolvedSupportCase
    (case_ : SupportCase) (resolvedAt : Timestamp) :
    Except ValidationError ResolvedSupportCase :=
  if hStatus : case_.status = SupportCaseStatus.Resolved then
    if hOpened : case_.openedAt ≤ resolvedAt then
      if hUpdated : case_.lastUpdatedAt ≤ resolvedAt then
        if hSla : resolvedAt ≤ case_.slaDueAt then
          Except.ok
            { case_ := case_
              resolvedAt := resolvedAt
              status_resolved := hStatus
              opened_le_resolved := hOpened
              lastUpdated_le_resolved := hUpdated
              resolved_by_sla := hSla }
        else
          Except.error ValidationError.crmInvariantFailed
      else
        Except.error ValidationError.crmInvariantFailed
    else
      Except.error ValidationError.crmInvariantFailed
  else
    Except.error ValidationError.crmInvariantFailed

/-- Validate a retention offer's account, coupon, segment, and discount caps. -/
def validateRetentionOffer
    (account : CRMAccount) (segment : CustomerSegment) (coupon : Coupon)
    (usesBefore : Nat) (discount : Money) :
    Except ValidationError RetentionOffer :=
  if hActive : crmAccountActive account then
    if hCoupon : couponCanBeApplied coupon account.lifetimeValue usesBefore then
      if hFloor : segment.minLifetimeValue ≤ account.lifetimeValue then
        if hDiscountCoupon : discount ≤ coupon.amount then
          if hCouponValue : coupon.amount ≤ account.lifetimeValue then
            if hSegment : discount ≤ segment.maxRetentionDiscount then
              Except.ok
                { account := account
                  segment := segment
                  coupon := coupon
                  usesBefore := usesBefore
                  discount := discount
                  account_active := hActive
                  coupon_applicable := hCoupon
                  account_meets_segment_value_floor := hFloor
                  discount_le_coupon := hDiscountCoupon
                  coupon_le_lifetimeValue := hCouponValue
                  discount_le_segment_cap := hSegment }
            else
              Except.error ValidationError.crmInvariantFailed
          else
            Except.error ValidationError.crmInvariantFailed
        else
          Except.error ValidationError.crmInvariantFailed
      else
        Except.error ValidationError.crmInvariantFailed
    else
      Except.error ValidationError.crmInvariantFailed
  else
    Except.error ValidationError.crmInvariantFailed

/-! ### Logistics validators -/

/--
Validate and normalize a shipment plan. The selected carrier quote supplies the
package and destination zone so those object equalities are definitional.
-/
def validateLogisticsShipmentPlan
    (id : ShipmentId) (order : Order) (fulfillment : DistinctFulfillmentPlan)
    (quote : CarrierQuote) (warehouse : Warehouse)
    (destinationId : Id) (postalCode : Nat)
    (plannedShipAt promisedDeliveryAt : Timestamp) :
    Except ValidationError LogisticsShipmentPlan :=
  if hEligible : orderEligibleForLogistics order then
    if hQuantity : fulfillment.requested = cartQuantityTotal order.items then
      if hSkus : allocationsMatchCartSkus order.items fulfillment.allocations then
        if hWarehouse : allocationsUseWarehouse warehouse fulfillment.allocations then
          if hWeight : cartWeightTotal order.items ≤ quote.package.weight then
            if hPromise : plannedShipAt ≤ promisedDeliveryAt then
              let destination : ShippingDestination :=
                { id := destinationId
                  zone := quote.service.zone
                  postalCode := postalCode }
              Except.ok
                { id := id
                  order := order
                  fulfillment := fulfillment
                  package := quote.package
                  quote := quote
                  warehouse := warehouse
                  destination := destination
                  plannedShipAt := plannedShipAt
                  promisedDeliveryAt := promisedDeliveryAt
                  order_eligible := hEligible
                  quantity_matches_cart := hQuantity
                  allocations_match_cart_skus := hSkus
                  allocations_use_warehouse := hWarehouse
                  quote_package_matches := rfl
                  quote_zone_matches_destination := rfl
                  package_covers_cart_weight := hWeight
                  planned_le_promised := hPromise }
            else
              Except.error ValidationError.logisticsInvariantFailed
          else
            Except.error ValidationError.logisticsInvariantFailed
        else
          Except.error ValidationError.logisticsInvariantFailed
      else
        Except.error ValidationError.logisticsInvariantFailed
    else
      Except.error ValidationError.logisticsInvariantFailed
  else
    Except.error ValidationError.logisticsInvariantFailed

/-- Successful shipment-plan validation proves allocation and carrier capacity safety. -/
theorem validateLogisticsShipmentPlan_sound
    {id : ShipmentId} {order : Order} {fulfillment : DistinctFulfillmentPlan}
    {quote : CarrierQuote} {warehouse : Warehouse} {destinationId : Id}
    {postalCode : Nat} {plannedShipAt promisedDeliveryAt : Timestamp}
    {plan : LogisticsShipmentPlan}
    (_h :
      validateLogisticsShipmentPlan id order fulfillment quote warehouse
          destinationId postalCode plannedShipAt promisedDeliveryAt =
        Except.ok plan) :
    plan.fulfillment.requested ≤
        allocationsAvailableTotal plan.fulfillment.allocations ∧
      plan.package.weight ≤ plan.quote.service.maxWeight := by
  exact ⟨shipmentPlan_requested_le_availableTotal plan,
    shipmentPlan_package_weight_safe plan⟩

/-- Validate concrete shipment identity and timestamp ordering. -/
def validateLogisticsShipment
    (id : ShipmentId) (plan : LogisticsShipmentPlan) (status : ShipmentStatus)
    (createdAt updatedAt : Timestamp) :
    Except ValidationError LogisticsShipment :=
  if hId : id = plan.id then
    if hUpdated : createdAt ≤ updatedAt then
      Except.ok
        { id := id
          plan := plan
          status := status
          createdAt := createdAt
          updatedAt := updatedAt
          id_matches_plan := hId
          created_le_updated := hUpdated }
    else
      Except.error ValidationError.logisticsInvariantFailed
  else
    Except.error ValidationError.logisticsInvariantFailed

/-- Validate and normalize a carrier handoff against the selected quote service. -/
def validateCarrierHandoff
    (plan : LogisticsShipmentPlan) (trackingNumber : Id)
    (handedOffAt acceptanceScanAt : Timestamp) :
    Except ValidationError CarrierHandoff :=
  if hPlanned : plan.plannedShipAt ≤ handedOffAt then
    if hAccepted : handedOffAt ≤ acceptanceScanAt then
      Except.ok
        { plan := plan
          service := plan.quote.service
          trackingNumber := trackingNumber
          handedOffAt := handedOffAt
          acceptanceScanAt := acceptanceScanAt
          service_matches_quote := rfl
          plannedShip_le_handedOff := hPlanned
          handedOff_le_acceptanceScan := hAccepted }
    else
      Except.error ValidationError.logisticsInvariantFailed
  else
    Except.error ValidationError.logisticsInvariantFailed

/-- Validate warehouse transfer source, warehouse, and quantity bounds. -/
def validateWarehouseTransfer
    (id : TransferId) (sku : Sku) (fromWarehouse toWarehouse : Warehouse)
    (sourceStock : StockState) (requested inTransit received : Quantity) :
    Except ValidationError WarehouseTransfer :=
  if hSku : sourceStock.sku = sku then
    if hWarehouses : fromWarehouse.id ≠ toWarehouse.id then
      if hRequested : requested ≤ availableStock sourceStock then
        if hInTransit : inTransit ≤ requested then
          if hReceived : received ≤ inTransit then
            Except.ok
              { id := id
                sku := sku
                fromWarehouse := fromWarehouse
                toWarehouse := toWarehouse
                sourceStock := sourceStock
                requested := requested
                inTransit := inTransit
                received := received
                source_sku_matches := hSku
                warehouses_distinct := hWarehouses
                requested_le_available := hRequested
                inTransit_le_requested := hInTransit
                received_le_inTransit := hReceived }
          else
            Except.error ValidationError.logisticsInvariantFailed
        else
          Except.error ValidationError.logisticsInvariantFailed
      else
        Except.error ValidationError.logisticsInvariantFailed
    else
      Except.error ValidationError.logisticsInvariantFailed
  else
    Except.error ValidationError.logisticsInvariantFailed

/-- Validate a return authorization against order, line, quantity, refund, and ledger checks. -/
def validateReturnAuthorization
    (id : ReturnAuthorizationId) (supportCase : SupportCase) (order : Order)
    (ledger : PaymentLedger) (status : ReturnAuthorizationStatus)
    (lines : List ReturnLine) (quantity : Quantity) (refundAmount : Money)
    (requestedAt decidedAt : Timestamp) :
    Except ValidationError ReturnAuthorization :=
  if hCase : supportCase.orderId = some order.id then
    if hSkus : returnLinesMatchOrderSkus order.items lines then
      if hQuantity : returnLinesQuantityTotal lines = quantity then
        if hRefundTotal : returnLinesRefundTotal lines = refundAmount then
          if hQuantityLe : quantity ≤ cartQuantityTotal order.items then
            if hRefund : canRefund ledger refundAmount then
              if hCaptured : ledger.captured = order.total then
                if hDecided : requestedAt ≤ decidedAt then
                  Except.ok
                    { id := id
                      supportCase := supportCase
                      order := order
                      ledger := ledger
                      status := status
                      lines := lines
                      quantity := quantity
                      refundAmount := refundAmount
                      requestedAt := requestedAt
                      decidedAt := decidedAt
                      support_case_matches_order := hCase
                      lines_match_order_skus := hSkus
                      quantity_correct := hQuantity
                      refund_correct := hRefundTotal
                      quantity_le_order_quantity := hQuantityLe
                      refundable := hRefund
                      captured_matches_order_total := hCaptured
                      requested_le_decided := hDecided }
                else
                  Except.error ValidationError.logisticsInvariantFailed
              else
                Except.error ValidationError.logisticsInvariantFailed
            else
              Except.error ValidationError.logisticsInvariantFailed
          else
            Except.error ValidationError.logisticsInvariantFailed
        else
          Except.error ValidationError.logisticsInvariantFailed
      else
        Except.error ValidationError.logisticsInvariantFailed
    else
      Except.error ValidationError.logisticsInvariantFailed
  else
    Except.error ValidationError.logisticsInvariantFailed

/-- Validate a physical return receipt against an approved authorization. -/
def validateReturnReceipt
    (authorization : ReturnAuthorization) (receivedQuantity : Quantity)
    (refundIssued : Money) (receivedAt : Timestamp) :
    Except ValidationError ReturnReceipt :=
  if hApproved : returnAuthorizationApproved authorization then
    if hReceived : receivedQuantity ≤ authorization.quantity then
      if hRefund : refundIssued ≤ authorization.refundAmount then
        if hTime : authorization.decidedAt ≤ receivedAt then
          Except.ok
            { authorization := authorization
              receivedQuantity := receivedQuantity
              refundIssued := refundIssued
              receivedAt := receivedAt
              authorization_approved := hApproved
              received_le_authorized := hReceived
              refund_le_authorized := hRefund
              decided_le_received := hTime }
        else
          Except.error ValidationError.logisticsInvariantFailed
      else
        Except.error ValidationError.logisticsInvariantFailed
    else
      Except.error ValidationError.logisticsInvariantFailed
  else
    Except.error ValidationError.logisticsInvariantFailed

/-! ### Cross-module wrapper validators -/

/-- Validate a bounded coupon application. -/
def validateBoundedCouponApplication
    (coupon : Coupon) (subtotal : Money) (usesBefore : Nat) :
    Except ValidationError BoundedCouponApplication :=
  if hApplicable : couponCanBeApplied coupon subtotal usesBefore then
    if hAmount : coupon.amount ≤ subtotal then
      Except.ok
        { coupon := coupon
          subtotal := subtotal
          usesBefore := usesBefore
          applicable := hApplicable
          amount_le_subtotal := hAmount }
    else
      Except.error ValidationError.implicitInvariantFailed
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate a captured payment against its order. -/
def validateCapturedPaymentMatchesOrder
    (order : Order) (payment : CapturedPayment) :
    Except ValidationError CapturedPaymentMatchesOrder :=
  if hOrder : payment.orderId = order.id then
    if hAmount : payment.amount = order.total then
      if hCurrency : payment.currency = order.currency then
        Except.ok
          { order := order
            payment := payment
            order_matches := hOrder
            amount_matches := hAmount
            currency_matches := hCurrency }
      else
        Except.error ValidationError.implicitInvariantFailed
    else
      Except.error ValidationError.implicitInvariantFailed
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate that a catalog entry is sellable. -/
def validateSellableCatalogEntry (entry : ProductCatalogEntry) :
    Except ValidationError SellableCatalogEntry :=
  if hProduct : productActive entry.product then
    if hVariant : variantActive entry.variant then
      Except.ok
        { entry := entry
          product_active := hProduct
          variant_active := hVariant }
    else
      Except.error ValidationError.implicitInvariantFailed
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate that a safe feed line is publishable. -/
def validatePublishableFeedLine (line : SafeProductFeedLine) :
    Except ValidationError PublishableFeedLine :=
  if hStock : feedLineHasStock line then
    Except.ok { line := line, has_stock := hStock }
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate sourceable distributor product quantity. -/
def validateSourceableDistributorProduct
    (product : DistributorProduct) (units : Quantity) :
    Except ValidationError SourceableDistributorProduct :=
  if hSource : distributorProductCanSource product units then
    Except.ok { product := product, units := units, can_source := hSource }
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate a coupon application against fraud-policy usage caps. -/
def validateFraudCheckedCouponApplication
    (application : BoundedCouponApplication) (policy : FraudPolicy) :
    Except ValidationError FraudCheckedCouponApplication :=
  if hUses : couponUsesAllowed policy application.usesBefore then
    Except.ok
      { application := application
        policy := policy
        uses_allowed := hUses }
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate and normalize a capture journal projection. -/
def validateCapturedPaymentJournalProjection
    (accounts : AccountingAccounts) (payment : CapturedPayment) :
    Except ValidationError CapturedPaymentJournalProjection :=
  let journal := paymentCapturedJournal accounts payment.amount
  Except.ok
    { accounts := accounts
      payment := payment
      journal := journal
      journal_correct := rfl }

/-- Validate and normalize a refund journal projection. -/
def validateRefundJournalProjection
    (accounts : AccountingAccounts) (ledger : PaymentLedger) (amount : Money) :
    Except ValidationError RefundJournalProjection :=
  if hRefund : canRefund ledger amount then
    let journal := refundIssuedJournal accounts amount
    Except.ok
      { accounts := accounts
        ledger := ledger
        amount := amount
        refundable := hRefund
        journal := journal
        journal_correct := rfl }
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate that a synced listing can be advertised. -/
def validateAdvertisableSyncedMarketplaceListing
    (synced : SyncedMarketplaceListing) :
    Except ValidationError AdvertisableSyncedMarketplaceListing :=
  if hAdvertise : listingCanBeAdvertised synced.listing then
    Except.ok { synced := synced, can_advertise := hAdvertise }
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate wholesale credit checkout totals, terms, and credit limit. -/
def validateWholesaleCreditCheckout
    (account : WholesaleCreditAccount) (lines : List WholesaleLine)
    (terms : PaymentTerms) (orderTotal : Money) :
    Except ValidationError WholesaleCreditCheckout :=
  if hTotal : orderTotal = wholesaleOrderNetTotal lines then
    if hTerms : paymentTermsAllowed TradeMode.Wholesale terms then
      if hCredit : canPlaceWholesaleCreditOrder account orderTotal then
        Except.ok
          { account := account
            lines := lines
            terms := terms
            orderTotal := orderTotal
            total_correct := hTotal
            terms_allowed := hTerms
            credit_ok := hCredit }
      else
        Except.error ValidationError.implicitInvariantFailed
    else
      Except.error ValidationError.implicitInvariantFailed
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate trusted, fresh competitor benchmark evidence. -/
def validateTrustedFreshCompetitorBenchmark
    (benchmark : CompetitorPriceBenchmark) (now : Timestamp)
    (maxAge : Duration) (trust : TrustLevel) :
    Except ValidationError TrustedFreshCompetitorBenchmark :=
  if hFresh : priceSnapshotFresh now maxAge benchmark.bestOffer.observedAt then
    if hTrust : trustAllowsAutoRepricing trust then
      Except.ok
        { benchmark := benchmark
          now := now
          maxAge := maxAge
          trust := trust
          fresh_best_offer := hFresh
          trust_allows_auto := hTrust }
    else
      Except.error ValidationError.implicitInvariantFailed
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate MAP compliance for a competitor-aware offer. -/
def validateMapCompliantCompetitorAwareOffer
    (offer : CompetitorAwareDropshipOffer) (policy : BrandPricingPolicy) :
    Except ValidationError MapCompliantCompetitorAwareOffer :=
  if hAdvertised : advertisedPriceAllowed policy offer.offer.saleUnitPrice then
    Except.ok
      { offer := offer
        policy := policy
        advertised_ok := hAdvertised }
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate fresh currency conversion evidence. -/
def validateFreshCurrencyConversion
    (sourceAmount : MoneyAmount) (rate : ExchangeRate)
    (targetAmount : MoneyAmount) (now : Timestamp) (maxAge : Duration) :
    Except ValidationError FreshCurrencyConversion :=
  if hSource : sourceAmount.currency = rate.source then
    if hTarget : targetAmount.currency = rate.target then
      if hAmount : targetAmount.amount = convertMoneyFloor sourceAmount.amount rate then
        if hFresh : fxQuoteFresh now maxAge rate then
          Except.ok
            { sourceAmount := sourceAmount
              rate := rate
              targetAmount := targetAmount
              now := now
              maxAge := maxAge
              source_matches_rate := hSource
              target_matches_rate := hTarget
              amount_correct := hAmount
              rate_fresh := hFresh }
        else
          Except.error ValidationError.implicitInvariantFailed
      else
        Except.error ValidationError.implicitInvariantFailed
    else
      Except.error ValidationError.implicitInvariantFailed
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate that a gift-card redemption is still within its expiry window. -/
def validateValidGiftCardRedemptionAt
    (now : Timestamp) (redemption : GiftCardRedemption) :
    Except ValidationError ValidGiftCardRedemptionAt :=
  if hValid : giftCardValidAt now redemption.card then
    Except.ok { now := now, redemption := redemption, not_expired := hValid }
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate a chargeback against a captured payment amount. -/
def validateChargebackForCapturedPayment
    (payment : CapturedPayment) (chargeback : Chargeback) :
    Except ValidationError ChargebackForCapturedPayment :=
  if hAmount : chargeback.paymentAmount = payment.amount then
    Except.ok
      { payment := payment
        chargeback := chargeback
        payment_amount_matches := hAmount }
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate that a demand forecast can drive automation. -/
def validateActionableDemandForecast
    (forecast : DemandForecast) :
    Except ValidationError ActionableDemandForecast :=
  if hActionable : demandForecastActionable forecast then
    Except.ok { forecast := forecast, actionable := hActionable }
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate approved supplier quality plus current orderability. -/
def validateApprovedOrderableSupplierQuality
    (quality : ApprovedSupplierQuality) :
    Except ValidationError ApprovedOrderableSupplierQuality :=
  if hOrders : supplierCanReceiveOrders quality.supplier then
    Except.ok { quality := quality, can_receive_orders := hOrders }
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate lead-to-opportunity conversion identity and amount caps. -/
def validateConvertedLeadOpportunity
    (lead : Lead) (opportunity : SalesOpportunity) :
    Except ValidationError ConvertedLeadOpportunity :=
  if hConverted : lead.status = LeadStatus.Converted then
    if hSource : opportunity.sourceLead = some lead.id then
      if hAccount : opportunity.accountId = lead.accountId then
        if hContact : opportunity.contactId = lead.contactId then
          if hCurrency : opportunity.currency = lead.currency then
            if hAmount : opportunity.amount ≤ lead.estimatedValue then
              Except.ok
                { lead := lead
                  opportunity := opportunity
                  lead_converted := hConverted
                  opportunity_source_matches := hSource
                  account_matches := hAccount
                  contact_matches := hContact
                  currency_matches := hCurrency
                  opportunity_amount_le_estimate := hAmount }
            else
              Except.error ValidationError.implicitInvariantFailed
          else
            Except.error ValidationError.implicitInvariantFailed
        else
          Except.error ValidationError.implicitInvariantFailed
      else
        Except.error ValidationError.implicitInvariantFailed
    else
      Except.error ValidationError.implicitInvariantFailed
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate a CRM-associated customer order. -/
def validateCRMOrderContact
    (account : CRMAccount) (contact : CRMContact) (order : Order) :
    Except ValidationError CRMOrderContact :=
  if hActive : crmAccountActive account then
    if hAccount : contact.accountId = account.id then
      if hCustomer : contact.customerId = account.customer.id then
        Except.ok
          { account := account
            contact := contact
            order := order
            account_active := hActive
            contact_account_matches := hAccount
            contact_customer_matches := hCustomer }
      else
        Except.error ValidationError.implicitInvariantFailed
    else
      Except.error ValidationError.implicitInvariantFailed
  else
    Except.error ValidationError.implicitInvariantFailed

/-- Validate escalation from a logistics exception into a CRM support case. -/
def validateLogisticsExceptionSupportCase
    (exception : LogisticsException) (shipment : LogisticsShipmentPlan)
    (supportCase : SupportCase) :
    Except ValidationError LogisticsExceptionSupportCase :=
  if hShipment : exception.shipmentId = shipment.id then
    if hOrder : supportCase.orderId = some shipment.order.id then
      if hStatus : supportCase.status = SupportCaseStatus.Escalated then
        if hOpened : exception.raisedAt ≤ supportCase.openedAt then
          Except.ok
            { exception := exception
              shipment := shipment
              supportCase := supportCase
              exception_shipment_matches := hShipment
              support_case_order_matches := hOrder
              support_case_escalated := hStatus
              exception_raised_before_case_opened := hOpened }
        else
          Except.error ValidationError.implicitInvariantFailed
      else
        Except.error ValidationError.implicitInvariantFailed
    else
      Except.error ValidationError.implicitInvariantFailed
  else
    Except.error ValidationError.implicitInvariantFailed

end CommerceTheory
