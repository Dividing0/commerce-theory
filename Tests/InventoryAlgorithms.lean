import CommerceTheory.InventoryAlgorithms

namespace CommerceTheory.Tests

def inventoryAlgorithmsSku : Sku :=
  { value := 5101 }

def inventoryAlgorithmsWarehouseA : Warehouse :=
  { id := 1
    name := "A" }

def inventoryAlgorithmsWarehouseB : Warehouse :=
  { id := 2
    name := "B" }

def inventoryAlgorithmsStockA : StockState :=
  { sku := inventoryAlgorithmsSku
    total := 10
    reserved := 4
    reserved_le_total := by norm_num }

def inventoryAlgorithmsStockB : StockState :=
  { sku := inventoryAlgorithmsSku
    total := 8
    reserved := 1
    reserved_le_total := by norm_num }

def inventoryAlgorithmsAllocationA : Allocation :=
  { node := { warehouse := inventoryAlgorithmsWarehouseA, stock := inventoryAlgorithmsStockA }
    quantity := 3
    quantity_le_available := by
      change 3 ≤ 10 - 4
      norm_num }

def inventoryAlgorithmsAllocationB : Allocation :=
  { node := { warehouse := inventoryAlgorithmsWarehouseB, stock := inventoryAlgorithmsStockB }
    quantity := 4
    quantity_le_available := by
      change 4 ≤ 8 - 1
      norm_num }

def inventoryAlgorithmsAllocations : List Allocation :=
  [inventoryAlgorithmsAllocationA, inventoryAlgorithmsAllocationB]

def timedAllocationExamplesPass : Bool :=
  (timedAllocationsTotal inventoryAlgorithmsAllocations).ret == 7 &&
    (timedAllocationsTotal inventoryAlgorithmsAllocations).time == 2 &&
    allocationsTotal inventoryAlgorithmsAllocations == 7 &&
    allocationsAvailableTotal inventoryAlgorithmsAllocations == 13

example : allocationKeysDistinct inventoryAlgorithmsAllocations := by
  simp [
    allocationKeysDistinct,
    inventoryAlgorithmsAllocations,
    inventoryAlgorithmsAllocationA,
    inventoryAlgorithmsAllocationB,
    inventoryAlgorithmsWarehouseA,
    inventoryAlgorithmsWarehouseB,
    inventoryAlgorithmsStockA,
    inventoryAlgorithmsStockB,
    inventoryAlgorithmsSku
  ]

example :
    ¬ allocationKeysDistinct
      [inventoryAlgorithmsAllocationA, inventoryAlgorithmsAllocationA] := by
  simp [
    allocationKeysDistinct,
    inventoryAlgorithmsAllocationA,
    inventoryAlgorithmsWarehouseA,
    inventoryAlgorithmsStockA,
    inventoryAlgorithmsSku
  ]

/-- info: true -/
#guard_msgs in
#eval timedAllocationExamplesPass

end CommerceTheory.Tests
