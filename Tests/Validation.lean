import CommerceTheory.Validation

namespace CommerceTheory.Tests

def testSku : Sku :=
  { value := 1001 }

def otherSku : Sku :=
  { value := 2002 }

def standardShipping : ShippingMethod :=
  { price := 500
    freeThreshold := 10000
    maxWeight := 20 }

def rawCartLine : RawCartLine :=
  { sku := testSku
    price := 2500
    cost := 1200
    quantity := 2
    discount := 500
    weight := 3 }

def rawCartLineWithOversizedDiscount : RawCartLine :=
  { rawCartLine with discount := 6000 }

def rawStock : RawStockState :=
  { sku := testSku
    total := 10
    reserved := 3 }

def rawFeedLine : RawProductFeedLine :=
  { sku := testSku
    channel := SalesChannel.MarketplaceChannel Marketplace.EtsyLike
    price := 1500
    currency := Currency.USD
    stock := 5
    stockState := rawStock
    pricePolicy :=
      { minPrice := 1000
        maxPrice := 2000 } }

def validRawOrder : RawOrder :=
  { id := { value := 1 }
    items := [rawCartLine]
    couponAmount := 1000
    shippingMethod := standardShipping
    tax := 350
    currency := Currency.USD
    status := OrderStatus.New
    total := 4350 }

def cartLineValidationAcceptsBoundedDiscount : Bool :=
  match validateCartLine rawCartLine with
  | Except.ok line =>
      lineGrossTotal line == 5000 &&
        lineNetTotal line == 4500 &&
        lineWeightTotal line == 6
  | Except.error _ => false

def cartLineValidationRejectsOversizedDiscount : Bool :=
  match validateCartLine rawCartLineWithOversizedDiscount with
  | Except.error ValidationError.lineDiscountExceedsGross => true
  | _ => false

def orderValidationAcceptsComputedTotal : Bool :=
  match validateOrder validRawOrder with
  | Except.ok order =>
      order.total == 4350 &&
        cartGrossTotal order.items == 5000 &&
        cartNetTotal order.items == 4500
  | Except.error _ => false

def orderValidationRejectsWrongTotal : Bool :=
  match validateOrder { validRawOrder with total := 4351 } with
  | Except.error ValidationError.orderTotalMismatch => true
  | _ => false

def orderValidationRejectsUnavailableShipping : Bool :=
  let overloadedShipping := { standardShipping with maxWeight := 5 }
  match validateOrder { validRawOrder with shippingMethod := overloadedShipping } with
  | Except.error ValidationError.shippingUnavailable => true
  | _ => false

def orderValidationRejectsOversizedCoupon : Bool :=
  match validateOrder { validRawOrder with couponAmount := 4501, total := 500 } with
  | Except.error ValidationError.couponExceedsSubtotal => true
  | _ => false

def feedValidationAcceptsSafeLine : Bool :=
  match validateFeedLine rawFeedLine with
  | Except.ok line =>
      line.sku == testSku &&
        line.stock == 5 &&
        availableStock line.stockState == 7
  | Except.error _ => false

def feedValidationRejectsSkuMismatch : Bool :=
  let mismatchedFeed :=
    { rawFeedLine with stockState := { rawStock with sku := otherSku } }
  match validateFeedLine mismatchedFeed with
  | Except.error ValidationError.feedSkuMismatch => true
  | _ => false

def refundValidationIssuesBoundedRefund : Bool :=
  match validatePaymentLedger { captured := 10000, refunded := 2500 } with
  | Except.ok ledger =>
      remainingRefundAmount ledger == 7500 &&
        match validateRefund { amount := 5000 } ledger with
        | Except.ok refund => (issueValidRefund refund).refunded == 7500
        | Except.error _ => false
  | Except.error _ => false

def refundValidationRejectsOverRefund : Bool :=
  match validatePaymentLedger { captured := 10000, refunded := 2500 } with
  | Except.ok ledger =>
      match validateRefund { amount := 8000 } ledger with
      | Except.error ValidationError.refundExceedsRemaining => true
      | _ => false
  | Except.error _ => false

def compareAndSwapValidationAcceptsCurrentVersion : Bool :=
  match validateVersionedStock rawStock 4 with
  | Except.ok stock =>
      match validateCompareAndSwapReservation stock 4 4 with
      | Except.ok next =>
          next.version == 5 &&
            next.reserved == 7 &&
            next.total == 10
      | Except.error _ => false
  | Except.error _ => false

def compareAndSwapValidationRejectsStaleVersion : Bool :=
  match validateVersionedStock rawStock 4 with
  | Except.ok stock =>
      match validateCompareAndSwapReservation stock 4 3 with
      | Except.error ValidationError.inventoryInvariantFailed => true
      | _ => false
  | Except.error _ => false

def logisticsShipping : ShippingMethod :=
  { price := 0
    freeThreshold := 10000
    maxWeight := 10 }

def logisticsRawLineA : RawCartLine :=
  { sku := testSku
    price := 1000
    cost := 500
    quantity := 1
    discount := 0
    weight := 2 }

def logisticsRawLineB : RawCartLine :=
  { sku := otherSku
    price := 1000
    cost := 500
    quantity := 1
    discount := 0
    weight := 2 }

def logisticsRawOrder : RawOrder :=
  { id := { value := 2 }
    items := [logisticsRawLineA, logisticsRawLineB]
    couponAmount := 0
    shippingMethod := logisticsShipping
    tax := 0
    currency := Currency.USD
    status := OrderStatus.Paid
    total := 2000 }

def logisticsWarehouse : Warehouse :=
  { id := 1, name := "Main" }

def logisticsStockA : StockState :=
  { sku := testSku
    total := 5
    reserved := 0
    reserved_le_total := by norm_num }

def logisticsStockB : StockState :=
  { sku := otherSku
    total := 5
    reserved := 0
    reserved_le_total := by norm_num }

def logisticsAllocationA1 : Allocation :=
  { node := { warehouse := logisticsWarehouse, stock := logisticsStockA }
    quantity := 1
    quantity_le_available := by norm_num [availableStock, logisticsStockA] }

def logisticsAllocationA2 : Allocation :=
  { node := { warehouse := logisticsWarehouse, stock := logisticsStockA }
    quantity := 2
    quantity_le_available := by norm_num [availableStock, logisticsStockA] }

def logisticsAllocationB1 : Allocation :=
  { node := { warehouse := logisticsWarehouse, stock := logisticsStockB }
    quantity := 1
    quantity_le_available := by norm_num [availableStock, logisticsStockB] }

def logisticsZoneA : ShippingZone :=
  { id := 1, name := "A" }

def logisticsZoneB : ShippingZone :=
  { id := 2, name := "B" }

def logisticsPackage : Package :=
  { weight := 4, volume := 1 }

def logisticsService : CarrierService :=
  { carrierId := 1
    zone := logisticsZoneA
    maxWeight := 10
    baseCost := 0
    promisedDays := days 2 }

def logisticsQuote : CarrierQuote :=
  { service := logisticsService
    package := logisticsPackage
    price := 100
    package_weight_ok := by norm_num [logisticsService, logisticsPackage]
    price_ge_cost := by norm_num [logisticsService] }

def logisticsDestinationA : ShippingDestination :=
  { id := 1, zone := logisticsZoneA, postalCode := 10001 }

def logisticsDestinationB : ShippingDestination :=
  { id := 2, zone := logisticsZoneB, postalCode := 10002 }

def logisticsValidationRejectsSkuQuantityMismatch : Bool :=
  match validateOrder logisticsRawOrder with
  | Except.ok order =>
      match validateDistinctFulfillmentPlan 2 [logisticsAllocationA2] with
      | Except.ok fulfillment =>
          match validateLogisticsShipmentPlan
              { value := 1 } order fulfillment logisticsQuote logisticsWarehouse
              logisticsDestinationA unixEpochTimestamp unixEpochTimestamp with
          | Except.error ValidationError.logisticsInvariantFailed => true
          | _ => false
      | Except.error _ => false
  | Except.error _ => false

def logisticsValidationRejectsDestinationZoneMismatch : Bool :=
  match validateOrder logisticsRawOrder with
  | Except.ok order =>
      match validateDistinctFulfillmentPlan 2 [logisticsAllocationA1, logisticsAllocationB1] with
      | Except.ok fulfillment =>
          match validateLogisticsShipmentPlan
              { value := 2 } order fulfillment logisticsQuote logisticsWarehouse
              logisticsDestinationB unixEpochTimestamp unixEpochTimestamp with
          | Except.error ValidationError.logisticsInvariantFailed => true
          | _ => false
      | Except.error _ => false
  | Except.error _ => false

def eventValidatorAcceptsPaidShip : Bool :=
  decide
    (orderEventValidator.mtr orderEventValidator.start
      [ OrderEventSymbol.OrderPlaced
      , OrderEventSymbol.PaymentCaptured
      , OrderEventSymbol.OrderShipped
      ] ∈ orderEventValidator.accept)

def eventValidatorAcceptsCapturedRefund : Bool :=
  decide
    (orderEventValidator.mtr orderEventValidator.start
      [ OrderEventSymbol.OrderPlaced
      , OrderEventSymbol.PaymentCaptured
      , OrderEventSymbol.RefundIssued
      ] ∈ orderEventValidator.accept)

def eventValidatorRejectsEmpty : Bool :=
  decide
    (orderEventValidator.mtr orderEventValidator.start [] ∉
      orderEventValidator.accept)

def eventValidatorRejectsPlacedOnly : Bool :=
  decide
    (orderEventValidator.mtr orderEventValidator.start
      [OrderEventSymbol.OrderPlaced] ∉ orderEventValidator.accept)

/-- info: true -/
#guard_msgs in
#eval cartLineValidationAcceptsBoundedDiscount

/-- info: true -/
#guard_msgs in
#eval cartLineValidationRejectsOversizedDiscount

/-- info: true -/
#guard_msgs in
#eval orderValidationAcceptsComputedTotal

/-- info: true -/
#guard_msgs in
#eval orderValidationRejectsWrongTotal

/-- info: true -/
#guard_msgs in
#eval orderValidationRejectsUnavailableShipping

/-- info: true -/
#guard_msgs in
#eval orderValidationRejectsOversizedCoupon

/-- info: true -/
#guard_msgs in
#eval feedValidationAcceptsSafeLine

/-- info: true -/
#guard_msgs in
#eval feedValidationRejectsSkuMismatch

/-- info: true -/
#guard_msgs in
#eval refundValidationIssuesBoundedRefund

/-- info: true -/
#guard_msgs in
#eval refundValidationRejectsOverRefund

/-- info: true -/
#guard_msgs in
#eval compareAndSwapValidationAcceptsCurrentVersion

/-- info: true -/
#guard_msgs in
#eval compareAndSwapValidationRejectsStaleVersion

/-- info: true -/
#guard_msgs in
#eval logisticsValidationRejectsSkuQuantityMismatch

/-- info: true -/
#guard_msgs in
#eval logisticsValidationRejectsDestinationZoneMismatch

/-- info: true -/
#guard_msgs in
#eval eventValidatorAcceptsPaidShip

/-- info: true -/
#guard_msgs in
#eval eventValidatorAcceptsCapturedRefund

/-- info: true -/
#guard_msgs in
#eval eventValidatorRejectsEmpty

/-- info: true -/
#guard_msgs in
#eval eventValidatorRejectsPlacedOnly

end CommerceTheory.Tests
