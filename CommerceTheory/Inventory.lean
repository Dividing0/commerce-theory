import CommerceTheory.Catalog

namespace CommerceTheory

/-! ## 2. Inventory, warehouse operations, allocation, and concurrency -/

/-!
Inventory safety is expressed as "reserved never exceeds total". Reservation
functions require a proof that enough stock is available, and return a new state
where the same invariant is still stored in the result.
-/

/-- Stock for one SKU, with the core invariant `reserved ≤ total`. -/
structure StockState where
  sku : Sku
  total : Quantity
  reserved : Quantity
  reserved_le_total : reserved ≤ total

/-- Sellable stock after subtracting reservations. -/
def availableStock (s : StockState) : Quantity :=
  s.total - s.reserved

/-- States the safety property captured by `availableStock_le_total`. -/
theorem availableStock_le_total (s : StockState) :
    availableStock s ≤ s.total := by
  unfold availableStock
  exact Nat.sub_le s.total s.reserved

/-- States the safety property captured by `availableStock_add_reserved_eq_total`. -/
theorem availableStock_add_reserved_eq_total (s : StockState) :
    availableStock s + s.reserved = s.total := by
  unfold availableStock
  exact Nat.sub_add_cancel s.reserved_le_total

/-- Computes or checks `canReserve` using the validated data in this module. -/
def canReserve (s : StockState) (q : Quantity) : Prop :=
  q ≤ availableStock s

/-- Reserve stock only when the caller supplies proof that the quantity fits. -/
def reserveStock (s : StockState) (q : Quantity) (h : canReserve s q) : StockState :=
  { sku := s.sku
    total := s.total
    reserved := s.reserved + q
    reserved_le_total := by
      unfold canReserve at h
      unfold availableStock at h
      exact Nat.add_le_of_le_sub' s.reserved_le_total h }

/-- States the safety property captured by `reserveStock_preserves_safety`. -/
theorem reserveStock_preserves_safety
    (s : StockState) (q : Quantity) (h : canReserve s q) :
    (reserveStock s q h).reserved ≤ (reserveStock s q h).total := by
  exact (reserveStock s q h).reserved_le_total

/-- Reserving stock adds exactly the requested quantity to the reserved count. -/
theorem reserveStock_reserved_eq
    (s : StockState) (q : Quantity) (h : canReserve s q) :
    (reserveStock s q h).reserved = s.reserved + q := by
  rfl

/-- A zero-quantity reservation is always permitted. -/
theorem canReserve_zero (s : StockState) :
    canReserve s 0 := by
  unfold canReserve
  exact Nat.zero_le (availableStock s)

/-- Data shape for `VersionedStock`; proof fields record invariants when needed. -/
structure VersionedStock extends StockState where
  version : Nat

/--
Optimistic-locking reservation. `expectedVersion` must match the current version,
and a successful reservation increments the version by one.
-/
def reserveVersionedStock
    (s : VersionedStock)
    (q expectedVersion : Nat)
    (_hVersion : expectedVersion = s.version)
    (hQty : canReserve s.toStockState q) : VersionedStock :=
  let next := reserveStock s.toStockState q hQty
  { sku := next.sku
    total := next.total
    reserved := next.reserved
    reserved_le_total := next.reserved_le_total
    version := s.version + 1 }

/-- States the safety property captured by `reserveVersionedStock_increases_version`. -/
theorem reserveVersionedStock_increases_version
    (s : VersionedStock) (q expectedVersion : Nat)
    (hVersion : expectedVersion = s.version)
    (hQty : canReserve s.toStockState q) :
    (reserveVersionedStock s q expectedVersion hVersion hQty).version = s.version + 1 := by
  rfl

/-- Optimistic-locking reservation preserves the stock safety invariant. -/
theorem reserveVersionedStock_preserves_safety
    (s : VersionedStock) (q expectedVersion : Nat)
    (hVersion : expectedVersion = s.version)
    (hQty : canReserve s.toStockState q) :
    (reserveVersionedStock s q expectedVersion hVersion hQty).reserved ≤
      (reserveVersionedStock s q expectedVersion hVersion hQty).total := by
  exact (reserveVersionedStock s q expectedVersion hVersion hQty).reserved_le_total

/-- Data shape for `Warehouse`; proof fields record invariants when needed. -/
structure Warehouse where
  id : Id
  name : String

/-- Data shape for `BinLocation`; proof fields record invariants when needed. -/
structure BinLocation where
  warehouse : Warehouse
  binId : Id

/-- Data shape for `BinStock`; proof fields record invariants when needed. -/
structure BinStock where
  sku : Sku
  location : BinLocation
  quantity : Quantity

/-- Data shape for `PickTask`; proof fields record invariants when needed. -/
structure PickTask where
  sku : Sku
  requested : Quantity
  bin : BinStock
  requested_le_bin_qty : requested ≤ bin.quantity

/-- States the safety property captured by `pickTask_safe`. -/
theorem pickTask_safe (t : PickTask) :
    t.requested ≤ t.bin.quantity := by
  exact t.requested_le_bin_qty

/-- Data shape for `PackTask`; proof fields record invariants when needed. -/
structure PackTask where
  picked : Quantity
  packed : Quantity
  packed_le_picked : packed ≤ picked

/-- States the safety property captured by `packTask_safe`. -/
theorem packTask_safe (t : PackTask) :
    t.packed ≤ t.picked := by
  exact t.packed_le_picked

/-- Data shape for `WarehouseShipment`; proof fields record invariants when needed. -/
structure WarehouseShipment where
  packed : Quantity
  shipped : Quantity
  shipped_le_packed : shipped ≤ packed

/-- States the safety property captured by `shipment_safe`. -/
theorem shipment_safe (s : WarehouseShipment) :
    s.shipped ≤ s.packed := by
  exact s.shipped_le_packed

/-- Data shape for `InventoryNode`; proof fields record invariants when needed. -/
structure InventoryNode where
  warehouse : Warehouse
  stock : StockState

/-- Data shape for `Allocation`; proof fields record invariants when needed. -/
structure Allocation where
  node : InventoryNode
  quantity : Quantity
  quantity_le_available : quantity ≤ availableStock node.stock

/-- Sum allocated quantities across warehouse nodes. -/
def allocationsTotal : List Allocation → Quantity
  | [] => 0
  | a :: rest => a.quantity + allocationsTotal rest

/-- Sum available quantities across the nodes referenced by allocations. -/
def allocationsAvailableTotal : List Allocation → Quantity
  | [] => 0
  | a :: rest => availableStock a.node.stock + allocationsAvailableTotal rest

/--
Allocation keys identify the warehouse/SKU bucket used by an allocation.
Distinct keys rule out double-counting the same warehouse stock for one SKU.
-/
def allocationKeysDistinct (allocations : List Allocation) : Prop :=
  (allocations.map fun a => (a.node.warehouse.id, a.node.stock.sku.value)).Nodup

/-- Allocation totals are bounded by the corresponding available-stock totals. -/
theorem allocationsTotal_le_availableTotal (allocations : List Allocation) :
    allocationsTotal allocations ≤ allocationsAvailableTotal allocations := by
  induction allocations with
  | nil =>
      simp [allocationsTotal, allocationsAvailableTotal]
  | cons a rest ih =>
      simpa [allocationsTotal, allocationsAvailableTotal] using
        Nat.add_le_add a.quantity_le_available ih

/-- A fulfillment plan is valid when allocations exactly cover the request. -/
structure FulfillmentPlan where
  requested : Quantity
  allocations : List Allocation
  total_eq_requested : allocationsTotal allocations = requested

/-- A fulfillment plan whose allocation keys cannot duplicate warehouse/SKU buckets. -/
structure DistinctFulfillmentPlan where
  requested : Quantity
  allocations : List Allocation
  total_eq_requested : allocationsTotal allocations = requested
  allocation_keys_distinct : allocationKeysDistinct allocations

/-- States the safety property captured by `allocation_safe`. -/
theorem allocation_safe (a : Allocation) :
    a.quantity ≤ availableStock a.node.stock := by
  exact a.quantity_le_available

/-- Any fulfillment plan's requested quantity is bounded by its available-stock total. -/
theorem fulfillmentPlan_requested_le_availableTotal (p : FulfillmentPlan) :
    p.requested ≤ allocationsAvailableTotal p.allocations := by
  rw [← p.total_eq_requested]
  exact allocationsTotal_le_availableTotal p.allocations

/-- Distinct fulfillment plans expose their no-duplicate warehouse/SKU guarantee. -/
theorem distinctFulfillmentPlan_keys_distinct (p : DistinctFulfillmentPlan) :
    allocationKeysDistinct p.allocations := by
  exact p.allocation_keys_distinct

/-- Distinct fulfillment plans also inherit the aggregate available-stock bound. -/
theorem distinctFulfillmentPlan_requested_le_availableTotal
    (p : DistinctFulfillmentPlan) :
    p.requested ≤ allocationsAvailableTotal p.allocations := by
  rw [← p.total_eq_requested]
  exact allocationsTotal_le_availableTotal p.allocations

/-! ### Concurrent reservations, expiry, and fulfillment safety -/

/-- Release reserved stock without shipping it, e.g. after cancellation or expiry. -/
def releaseReservedStock
    (s : StockState) (q : Quantity) (_hReserved : q ≤ s.reserved) :
    StockState :=
  { sku := s.sku
    total := s.total
    reserved := s.reserved - q
    reserved_le_total := by
      exact (Nat.sub_le s.reserved q).trans s.reserved_le_total }

/-- Releasing a reservation preserves the stock safety invariant. -/
theorem releaseReservedStock_preserves_safety
    (s : StockState) (q : Quantity) (hReserved : q ≤ s.reserved) :
    (releaseReservedStock s q hReserved).reserved ≤
      (releaseReservedStock s q hReserved).total := by
  exact (releaseReservedStock s q hReserved).reserved_le_total

/-- Releasing a reservation subtracts exactly the released quantity from reserved stock. -/
theorem releaseReservedStock_reserved_eq
    (s : StockState) (q : Quantity) (hReserved : q ≤ s.reserved) :
    (releaseReservedStock s q hReserved).reserved = s.reserved - q := by
  rfl

/--
Confirm a shipment from stock that was already reserved. Both total and reserved
stock decrease, so sellable availability is not charged a second time.
-/
def confirmReservedShipment
    (s : StockState) (q : Quantity) (_hReserved : q ≤ s.reserved) :
    StockState :=
  { sku := s.sku
    total := s.total - q
    reserved := s.reserved - q
    reserved_le_total := by
      exact Nat.sub_le_sub_right s.reserved_le_total q }

/-- Confirming a reserved shipment preserves stock safety. -/
theorem confirmReservedShipment_preserves_safety
    (s : StockState) (q : Quantity) (hReserved : q ≤ s.reserved) :
    (confirmReservedShipment s q hReserved).reserved ≤
      (confirmReservedShipment s q hReserved).total := by
  exact (confirmReservedShipment s q hReserved).reserved_le_total

/--
Confirmed shipment from already-reserved stock does not reduce available stock a
second time: reservation lowered availability, confirmation consumes the held
units.
-/
theorem confirmReservedShipment_available_eq
    (s : StockState) (q : Quantity) (hReserved : q ≤ s.reserved) :
    availableStock (confirmReservedShipment s q hReserved) = availableStock s := by
  unfold availableStock confirmReservedShipment
  omega

/-- Compare-and-swap reservation: stale versions or insufficient stock fail. -/
def compareAndSwapReserve?
    (s : VersionedStock) (q expectedVersion : Nat) : Option VersionedStock :=
  if hVersion : expectedVersion = s.version then
    if hQty : canReserve s.toStockState q then
      some (reserveVersionedStock s q expectedVersion hVersion hQty)
    else
      none
  else
    none

/-- Compare-and-swap rejects stale expected versions. -/
theorem compareAndSwapReserve?_stale_fails
    (s : VersionedStock) (q expectedVersion : Nat)
    (hStale : expectedVersion ≠ s.version) :
    compareAndSwapReserve? s q expectedVersion = none := by
  simp [compareAndSwapReserve?, hStale]

/-- Compare-and-swap rejects requests that do not fit available stock. -/
theorem compareAndSwapReserve?_insufficient_stock_fails
    (s : VersionedStock) (q expectedVersion : Nat)
    (hVersion : expectedVersion = s.version)
    (hQty : ¬ canReserve s.toStockState q) :
    compareAndSwapReserve? s q expectedVersion = none := by
  simp [compareAndSwapReserve?, hVersion, hQty]

/-- Successful compare-and-swap reservations increment the version exactly once. -/
theorem compareAndSwapReserve?_success_increases_version
    (s : VersionedStock) (q expectedVersion : Nat) (next : VersionedStock)
    (h : compareAndSwapReserve? s q expectedVersion = some next) :
    next.version = s.version + 1 := by
  by_cases hVersion : expectedVersion = s.version
  · by_cases hQty : canReserve s.toStockState q
    · simp [compareAndSwapReserve?, hVersion, hQty] at h
      cases h
      rfl
    · simp [compareAndSwapReserve?, hVersion, hQty] at h
  · simp [compareAndSwapReserve?, hVersion] at h

/-- Successful compare-and-swap reservations preserve stock safety. -/
theorem compareAndSwapReserve?_success_preserves_safety
    (s : VersionedStock) (q expectedVersion : Nat) (next : VersionedStock)
    (h : compareAndSwapReserve? s q expectedVersion = some next) :
    next.reserved ≤ next.total := by
  by_cases hVersion : expectedVersion = s.version
  · by_cases hQty : canReserve s.toStockState q
    · simp [compareAndSwapReserve?, hVersion, hQty] at h
      cases h
      exact
        (reserveVersionedStock s q expectedVersion hVersion hQty).reserved_le_total
    · simp [compareAndSwapReserve?, hVersion, hQty] at h
  · simp [compareAndSwapReserve?, hVersion] at h

/-- A version used for a successful reservation is stale for the next stock state. -/
theorem reservation_original_version_stale_after_success
    (s : VersionedStock) (q expectedVersion : Nat)
    (hVersion : expectedVersion = s.version)
    (hQty : canReserve s.toStockState q) :
    expectedVersion ≠
      (reserveVersionedStock s q expectedVersion hVersion hQty).version := by
  rw [reserveVersionedStock_increases_version s q expectedVersion hVersion hQty,
    hVersion]
  exact Nat.ne_of_lt (Nat.lt_add_one s.version)

/-- A second request using the original version is rejected after the first succeeds. -/
theorem compareAndSwapReserve?_original_version_stale_after_reservation
    (s : VersionedStock) (q expectedVersion nextQuantity : Nat)
    (hVersion : expectedVersion = s.version)
    (hQty : canReserve s.toStockState q) :
    compareAndSwapReserve?
        (reserveVersionedStock s q expectedVersion hVersion hQty)
        nextQuantity
        expectedVersion =
      none := by
  exact compareAndSwapReserve?_stale_fails
    (reserveVersionedStock s q expectedVersion hVersion hQty)
    nextQuantity
    expectedVersion
    (reservation_original_version_stale_after_success s q expectedVersion
      hVersion hQty)

/-- A reservation attempt as seen by a concurrent client. -/
structure ReservationAttempt where
  stock : VersionedStock
  quantity : Quantity
  expectedVersion : Nat

/-- Commit a reservation attempt using compare-and-swap semantics. -/
def commitReservationAttempt? (attempt : ReservationAttempt) : Option VersionedStock :=
  compareAndSwapReserve? attempt.stock attempt.quantity attempt.expectedVersion

/-- Concurrent attempts conflict when they target the same SKU and observed version. -/
structure ConcurrentReservationConflict where
  first : ReservationAttempt
  second : ReservationAttempt
  same_sku : first.stock.sku = second.stock.sku
  same_observed_version : first.expectedVersion = second.expectedVersion

/-- Concurrent conflicts expose that both attempts target the same SKU. -/
theorem concurrentReservationConflict_same_sku
    (conflict : ConcurrentReservationConflict) :
    conflict.first.stock.sku = conflict.second.stock.sku := by
  exact conflict.same_sku

/-- Concurrent conflicts expose the shared observed version. -/
theorem concurrentReservationConflict_same_expected_version
    (conflict : ConcurrentReservationConflict) :
    conflict.first.expectedVersion = conflict.second.expectedVersion := by
  exact conflict.same_observed_version

/-- After the first conflicting attempt succeeds, the second observed version is stale. -/
theorem concurrentReservationConflict_second_version_stale_after_first
    (conflict : ConcurrentReservationConflict)
    (hFirstVersion : conflict.first.expectedVersion = conflict.first.stock.version)
    (hFirstQty : canReserve conflict.first.stock.toStockState conflict.first.quantity) :
    conflict.second.expectedVersion ≠
      (reserveVersionedStock
        conflict.first.stock
        conflict.first.quantity
        conflict.first.expectedVersion
        hFirstVersion
        hFirstQty).version := by
  rw [← conflict.same_observed_version]
  exact reservation_original_version_stale_after_success
    conflict.first.stock
    conflict.first.quantity
    conflict.first.expectedVersion
    hFirstVersion
    hFirstQty

/-- Reservation lifecycle states relevant to inventory availability. -/
inductive ReservationStatus where
  | Active
  | Expired
  | Confirmed
  | Released
deriving DecidableEq, Repr

/-- A reservation with expiry and enough reserved stock to release or confirm. -/
structure TimedReservation where
  stock : StockState
  quantity : Quantity
  reservedAt : Timestamp
  expiresAt : Timestamp
  status : ReservationStatus
  reserved_at_le_expires : reservedAt ≤ expiresAt
  quantity_le_reserved : quantity ≤ stock.reserved

/-- A reservation is expired when the current time is after its expiry instant. -/
def reservationExpiredAt (now : Timestamp) (reservation : TimedReservation) : Prop :=
  reservation.expiresAt < now

/-- A reservation is active at a time when it has not passed its expiry instant. -/
def reservationActiveAt (now : Timestamp) (reservation : TimedReservation) : Prop :=
  reservation.status = ReservationStatus.Active ∧ now ≤ reservation.expiresAt

/-- Expired reservations cannot also be active at the same timestamp. -/
theorem expiredReservation_not_activeAt
    (reservation : TimedReservation) (now : Timestamp)
    (hExpired : reservationExpiredAt now reservation) :
    ¬ reservationActiveAt now reservation := by
  intro hActive
  exact (not_lt_of_ge hActive.right) hExpired

/-- Releasing an expired reservation frees its held reserved quantity. -/
def releaseExpiredReservation
    (reservation : TimedReservation) (now : Timestamp)
    (_hExpired : reservationExpiredAt now reservation) :
    StockState :=
  releaseReservedStock
    reservation.stock
    reservation.quantity
    reservation.quantity_le_reserved

/-- Releasing an expired reservation preserves stock safety. -/
theorem releaseExpiredReservation_preserves_safety
    (reservation : TimedReservation) (now : Timestamp)
    (hExpired : reservationExpiredAt now reservation) :
    (releaseExpiredReservation reservation now hExpired).reserved ≤
      (releaseExpiredReservation reservation now hExpired).total := by
  exact (releaseExpiredReservation reservation now hExpired).reserved_le_total

/-- Backorder quantity conservation: request equals available-now plus backordered. -/
structure BackorderRequest where
  sku : Sku
  requested : Quantity
  availableNow : Quantity
  backordered : Quantity
  requested_eq_available_plus_backordered : requested = availableNow + backordered

/-- Backorder requests conserve requested quantity across immediate and delayed units. -/
theorem backorderRequest_conserves_quantity (request : BackorderRequest) :
    request.availableNow + request.backordered = request.requested := by
  exact request.requested_eq_available_plus_backordered.symm

/-- Backordered quantity cannot exceed the original request. -/
theorem backorderRequest_backordered_le_requested (request : BackorderRequest) :
    request.backordered ≤ request.requested := by
  rw [request.requested_eq_available_plus_backordered]
  omega

/-- A preorder window with capacity and timestamp ordering. -/
structure PreorderWindow where
  sku : Sku
  opensAt : Timestamp
  closesAt : Timestamp
  capacity : Quantity
  opens_le_closes : opensAt ≤ closesAt

/-- A preorder reservation must fit inside the declared window capacity. -/
structure PreorderReservation where
  window : PreorderWindow
  quantity : Quantity
  reservedAt : Timestamp
  quantity_le_capacity : quantity ≤ window.capacity
  reserved_in_window : window.opensAt ≤ reservedAt ∧ reservedAt ≤ window.closesAt

/-- Preorder reservations are bounded by their window capacity. -/
theorem preorderReservation_quantity_le_capacity
    (reservation : PreorderReservation) :
    reservation.quantity ≤ reservation.window.capacity := by
  exact reservation.quantity_le_capacity

/-- Preorder reservation timestamps are inside the preorder window. -/
theorem preorderReservation_in_window
    (reservation : PreorderReservation) :
    reservation.window.opensAt ≤ reservation.reservedAt ∧
      reservation.reservedAt ≤ reservation.window.closesAt := by
  exact reservation.reserved_in_window

/-- Serial numbers identify individual inventory units. -/
structure SerialNumber where
  value : Nat
deriving DecidableEq, Repr

/-- A serial-numbered physical inventory unit. -/
structure SerializedInventoryUnit where
  sku : Sku
  serial : SerialNumber
  warehouse : Warehouse
  reserved : Bool

/-- Serialized inventory cannot contain duplicate serial numbers. -/
def serialNumbersDistinct (units : List SerializedInventoryUnit) : Prop :=
  (units.map fun unit => unit.serial.value).Nodup

/-- A proof-carrying set of serialized inventory units. -/
structure SerializedInventorySet where
  units : List SerializedInventoryUnit
  serials_distinct : serialNumbersDistinct units

/-- Serialized inventory sets expose unique serial numbers. -/
theorem serializedInventorySet_serials_distinct
    (inventory : SerializedInventorySet) :
    serialNumbersDistinct inventory.units := by
  exact inventory.serials_distinct

/-- Lot/batch inventory, including expiry for perishable or regulated goods. -/
structure InventoryLot where
  sku : Sku
  lotId : Id
  warehouse : Warehouse
  expiresAt : Timestamp
  quantity : Quantity

/-- A lot is usable when it has positive quantity and is not expired. -/
def lotUsableAt (now : Timestamp) (lot : InventoryLot) : Prop :=
  now ≤ lot.expiresAt ∧ 0 < lot.quantity

/-- Expired lots cannot be used at the same timestamp. -/
theorem expiredLot_not_usableAt
    (lot : InventoryLot) (now : Timestamp)
    (hExpired : lot.expiresAt < now) :
    ¬ lotUsableAt now lot := by
  intro hUsable
  exact (not_lt_of_ge hUsable.left) hExpired

/-- SKU substitution rule backed by available substitute stock. -/
structure SkuSubstitution where
  requestedSku : Sku
  substituteSku : Sku
  substituteStock : StockState
  maxSubstituteQty : Quantity
  substitute_sku_matches : substituteStock.sku = substituteSku
  max_qty_le_substitute_available : maxSubstituteQty ≤ availableStock substituteStock

/-- Substitution rules cannot offer more substitute quantity than available stock. -/
theorem skuSubstitution_max_qty_le_available
    (rule : SkuSubstitution) :
    rule.maxSubstituteQty ≤ availableStock rule.substituteStock := by
  exact rule.max_qty_le_substitute_available

/-- Warehouse ids referenced by a fulfillment allocation list. -/
def allocationWarehouseIds (allocations : List Allocation) : List Id :=
  allocations.map fun allocation => allocation.node.warehouse.id

/-- A distinct fulfillment plan that is explicitly split across two warehouses. -/
structure SplitFulfillmentPlan where
  plan : DistinctFulfillmentPlan
  firstWarehouse : Warehouse
  secondWarehouse : Warehouse
  first_warehouse_used : firstWarehouse.id ∈ allocationWarehouseIds plan.allocations
  second_warehouse_used : secondWarehouse.id ∈ allocationWarehouseIds plan.allocations
  warehouses_distinct : firstWarehouse.id ≠ secondWarehouse.id

/-- Split fulfillment inherits aggregate available-stock safety. -/
theorem splitFulfillmentPlan_requested_le_availableTotal
    (plan : SplitFulfillmentPlan) :
    plan.plan.requested ≤ allocationsAvailableTotal plan.plan.allocations := by
  exact distinctFulfillmentPlan_requested_le_availableTotal plan.plan

/-- Split fulfillment plans expose their cross-warehouse witness. -/
theorem splitFulfillmentPlan_warehouses_distinct
    (plan : SplitFulfillmentPlan) :
    plan.firstWarehouse.id ≠ plan.secondWarehouse.id := by
  exact plan.warehouses_distinct

/-- Split fulfillment still uses distinct warehouse/SKU allocation keys. -/
theorem splitFulfillmentPlan_allocation_keys_distinct
    (plan : SplitFulfillmentPlan) :
    allocationKeysDistinct plan.plan.allocations := by
  exact plan.plan.allocation_keys_distinct

end CommerceTheory
