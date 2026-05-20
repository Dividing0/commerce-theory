import CommerceTheory.Inventory
import Cslib.Algorithms.Lean.TimeM

namespace CommerceTheory

/-! ## CSLib timed inventory algorithms -/

/-!
`TimeM` lets the theory state small executable algorithms with an explicit cost
model.  Here each allocation row costs one unit to inspect.
-/

/-- Sum allocation quantities while counting one operation per allocation row. -/
def timedAllocationsTotal : List Allocation → Cslib.Algorithms.Lean.TimeM Nat Quantity
  | [] => pure 0
  | allocation :: rest => do
      Cslib.Algorithms.Lean.TimeM.tick 1
      let subtotal ← timedAllocationsTotal rest
      pure (allocation.quantity + subtotal)

/-- The timed allocation sum computes the same value as the existing specification. -/
theorem timedAllocationsTotal_ret (allocations : List Allocation) :
    (timedAllocationsTotal allocations).ret = allocationsTotal allocations := by
  induction allocations with
  | nil =>
      simp [timedAllocationsTotal, allocationsTotal]
  | cons allocation rest ih =>
      simp [timedAllocationsTotal, allocationsTotal, ih]

/-- The allocation summation cost is exactly one tick per allocation row. -/
theorem timedAllocationsTotal_time (allocations : List Allocation) :
    (timedAllocationsTotal allocations).time = allocations.length := by
  induction allocations with
  | nil =>
      simp [timedAllocationsTotal]
  | cons allocation rest ih =>
      simp [timedAllocationsTotal, ih, Nat.add_comm]

/-- The timed allocation sum inherits the existing available-stock safety bound. -/
theorem timedAllocationsTotal_le_availableTotal (allocations : List Allocation) :
    (timedAllocationsTotal allocations).ret ≤ allocationsAvailableTotal allocations := by
  rw [timedAllocationsTotal_ret]
  exact allocationsTotal_le_availableTotal allocations

end CommerceTheory
