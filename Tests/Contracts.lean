import CommerceTheory.Validation
import CommerceTheory.Workflow

namespace CommerceTheory.Tests

def contractStock : StockState :=
  { sku := { value := 3003 }
    total := 10
    reserved := 3
    reserved_le_total := by norm_num }

def contractCanReserveTwo : canReserve contractStock 2 := by
  decide

def contractReservedStock : StockState :=
  reserveStock contractStock 2 contractCanReserveTwo

example : contractReservedStock.reserved = 5 := by
  rfl

example : contractReservedStock.reserved ≤ contractReservedStock.total := by
  exact contractReservedStock.reserved_le_total

example : ¬ CanOrderTransition OrderStatus.Cancelled OrderStatus.Delivered := by
  exact cancelled_cannot_become_delivered

example : orderStatusLTS.CanReach OrderStatus.New OrderStatus.Delivered := by
  exact new_order_can_reach_delivered

example : ¬ orderStatusLTS.CanReach OrderStatus.Cancelled OrderStatus.Delivered := by
  exact cancelled_order_cannot_reach_delivered

def createdPayment : TypedPayment PaymentState.Created :=
  { id := { value := 1 }
    orderId := { value := 10 }
    amount := 4350
    currency := Currency.USD
    amount_pos := by norm_num }

def authorizedPayment : TypedPayment PaymentState.Authorized :=
  authorizePayment createdPayment

def capturedPayment : TypedPayment PaymentState.Captured :=
  (capturePayment authorizedPayment).1

def capturedReceipt : CapturedPayment :=
  (capturePayment authorizedPayment).2

example : capturedPayment.amount = createdPayment.amount := by
  rfl

example : capturedReceipt.amount = createdPayment.amount := by
  rfl

end CommerceTheory.Tests
