import WebshopTheory.Catalog

namespace WebShopTheoryComplete

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
  omega

/-- States the safety property captured by `availableStock_add_reserved_eq_total`. -/
theorem availableStock_add_reserved_eq_total (s : StockState) :
    availableStock s + s.reserved = s.total := by
  unfold availableStock
  have h := s.reserved_le_total
  omega

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
      have hs := s.reserved_le_total
      omega }

/-- States the safety property captured by `reserveStock_preserves_safety`. -/
theorem reserveStock_preserves_safety
    (s : StockState) (q : Quantity) (h : canReserve s q) :
    (reserveStock s q h).reserved ≤ (reserveStock s q h).total := by
  exact (reserveStock s q h).reserved_le_total

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
    (hVersion : expectedVersion = s.version)
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

/-- A fulfillment plan is valid when allocations exactly cover the request. -/
structure FulfillmentPlan where
  requested : Quantity
  allocations : List Allocation
  total_eq_requested : allocationsTotal allocations = requested

/-- States the safety property captured by `allocation_safe`. -/
theorem allocation_safe (a : Allocation) :
    a.quantity ≤ availableStock a.node.stock := by
  exact a.quantity_le_available


end WebShopTheoryComplete
