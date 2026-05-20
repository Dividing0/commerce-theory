import CommerceTheory.Inventory
import Cslib.Foundations.Data.FinFun

namespace CommerceTheory

/-! ## CSLib finite-support keyed totals -/

/-!
Several commerce invariants are naturally keyed by sparse business identifiers.
CSLib `FinFun` gives those sparse totals an explicit finite support instead of
leaving key scope implicit in list folds.
-/

/-- Warehouse/SKU bucket used for keyed allocation totals. -/
abbrev AllocationKey := Nat × Nat

/-- Extract the warehouse/SKU bucket from an allocation. -/
def allocationKey (allocation : Allocation) : AllocationKey :=
  (allocation.node.warehouse.id, allocation.node.stock.sku.value)

/-- The finite set of allocation keys present in a list. -/
def allocationKeySupport (allocations : List Allocation) : Finset AllocationKey :=
  (allocations.map allocationKey).toFinset

/-- Sum only the allocation rows that belong to a specific warehouse/SKU bucket. -/
def allocationQuantityForKey : List Allocation → AllocationKey → Quantity
  | [], _key => 0
  | allocation :: rest, key =>
      if allocationKey allocation = key then
        allocation.quantity + allocationQuantityForKey rest key
      else
        allocationQuantityForKey rest key

/-- Sparse finite-support map from warehouse/SKU bucket to allocated quantity. -/
def allocationQuantityByKey
    (allocations : List Allocation) : Cslib.FinFun AllocationKey Quantity :=
  Cslib.FinFun.fromFun
    (allocationQuantityForKey allocations)
    (allocationKeySupport allocations)

/-- Keys absent from the allocation list read as zero in the finite-support map. -/
theorem allocationQuantityByKey_zero_of_key_not_present
    (allocations : List Allocation) (key : AllocationKey)
    (h : key ∉ allocationKeySupport allocations) :
    allocationQuantityByKey allocations key = 0 := by
  unfold allocationQuantityByKey
  simp [Cslib.FinFun.coe_eq_fn, Cslib.FinFun.fromFun_fn, h]

/-- Present keys read as the corresponding filtered allocation total. -/
theorem allocationQuantityByKey_eq_for_present_key
    (allocations : List Allocation) (key : AllocationKey)
    (h : key ∈ allocationKeySupport allocations) :
    allocationQuantityByKey allocations key = allocationQuantityForKey allocations key := by
  unfold allocationQuantityByKey
  simp [Cslib.FinFun.coe_eq_fn, Cslib.FinFun.fromFun_fn, h]

/-- A single keyed total cannot exceed the aggregate allocation total. -/
theorem allocationQuantityForKey_le_total
    (allocations : List Allocation) (key : AllocationKey) :
    allocationQuantityForKey allocations key ≤ allocationsTotal allocations := by
  induction allocations with
  | nil =>
      simp [allocationQuantityForKey, allocationsTotal]
  | cons allocation rest ih =>
      by_cases hkey : allocationKey allocation = key
      · simp [allocationQuantityForKey, allocationsTotal, hkey]
        exact ih
      · simp [allocationQuantityForKey, allocationsTotal, hkey]
        exact ih.trans (Nat.le_add_left (allocationsTotal rest) allocation.quantity)

/-- A finite-support keyed allocation total is bounded by total allocated quantity. -/
theorem allocationQuantityByKey_le_total
    (allocations : List Allocation) (key : AllocationKey) :
    allocationQuantityByKey allocations key ≤ allocationsTotal allocations := by
  by_cases h : key ∈ allocationKeySupport allocations
  · rw [allocationQuantityByKey_eq_for_present_key allocations key h]
    exact allocationQuantityForKey_le_total allocations key
  · rw [allocationQuantityByKey_zero_of_key_not_present allocations key h]
    exact Nat.zero_le (allocationsTotal allocations)

end CommerceTheory
