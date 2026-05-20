import WebshopTheory.Pricing

namespace WebShopTheoryComplete

/-! ## 4. Orders, payments, refunds, typestate, and status machines -/

/-!
This module models order and payment lifecycles. Plain status enums describe
runtime state, while `TypedOrder` and `TypedPayment` encode the state in the
type itself. That lets functions such as `capturePayment` accept only authorized
payments and return only captured payments.
-/

/-- Closed set of cases for `OrderStatus` in the webshop domain model. -/
inductive OrderStatus where
  | New
  | Paid
  | Packed
  | Shipped
  | Delivered
  | Cancelled
  | Refunded
  | Backordered
deriving DecidableEq, Repr

/-- A validated order stores proof that shipping and total calculations are correct. -/
structure Order where
  id : OrderId
  items : List CartLine
  couponAmount : Money
  shippingMethod : ShippingMethod
  tax : Money
  currency : Currency
  status : OrderStatus
  total : Money
  shipping_available : shippingAvailable shippingMethod (cartWeightTotal items)
  total_correct : total = orderTotal shippingMethod couponAmount tax items

/-- Any validated order inherits the pricing bound proved in the pricing module. -/
theorem order_total_is_safe (order : Order) :
    order.total ≤ cartGrossTotal order.items + order.shippingMethod.price + order.tax := by
  calc
    order.total = orderTotal order.shippingMethod order.couponAmount order.tax order.items := by
      exact order.total_correct
    _ ≤ cartGrossTotal order.items + order.shippingMethod.price + order.tax := by
      exact orderTotal_le_gross_plus_shipping_plus_tax
        order.shippingMethod order.couponAmount order.tax order.items

/-- The allowed order status transitions, written as an explicit relation. -/
inductive CanOrderTransition : OrderStatus → OrderStatus → Prop where
  | new_paid : CanOrderTransition OrderStatus.New OrderStatus.Paid
  | new_cancelled : CanOrderTransition OrderStatus.New OrderStatus.Cancelled
  | new_backordered : CanOrderTransition OrderStatus.New OrderStatus.Backordered
  | paid_packed : CanOrderTransition OrderStatus.Paid OrderStatus.Packed
  | paid_refunded : CanOrderTransition OrderStatus.Paid OrderStatus.Refunded
  | packed_shipped : CanOrderTransition OrderStatus.Packed OrderStatus.Shipped
  | shipped_delivered : CanOrderTransition OrderStatus.Shipped OrderStatus.Delivered
  | delivered_refunded : CanOrderTransition OrderStatus.Delivered OrderStatus.Refunded
  | backordered_paid : CanOrderTransition OrderStatus.Backordered OrderStatus.Paid
  | backordered_cancelled : CanOrderTransition OrderStatus.Backordered OrderStatus.Cancelled

/-- States the safety property captured by `delivered_cannot_become_paid`. -/
theorem delivered_cannot_become_paid :
    ¬ CanOrderTransition OrderStatus.Delivered OrderStatus.Paid := by
  intro h
  cases h

/-- States the safety property captured by `cancelled_has_no_outgoing`. -/
theorem cancelled_has_no_outgoing (next : OrderStatus) :
    ¬ CanOrderTransition OrderStatus.Cancelled next := by
  intro h
  cases h

/-- Data shape for `TypedOrder`; proof fields record invariants when needed. -/
structure TypedOrder (s : OrderStatus) where
  id : OrderId
  total : Money
  currency : Currency
  total_pos : 0 < total

/-- Data shape for `CapturedPayment`; proof fields record invariants when needed. -/
structure CapturedPayment where
  orderId : OrderId
  amount : Money
  currency : Currency

/-- Closed set of cases for `PaymentState` in the webshop domain model. -/
inductive PaymentState where
  | Created
  | Authorized
  | Captured
  | Failed
  | Voided
  | Refunded
deriving DecidableEq, Repr

/-- A payment value whose current lifecycle state is part of its Lean type. -/
structure TypedPayment (s : PaymentState) where
  id : PaymentId
  orderId : OrderId
  amount : Money
  currency : Currency
  amount_pos : 0 < amount

/-- Computes or checks `authorizePayment` using the validated data in this module. -/
def authorizePayment (p : TypedPayment PaymentState.Created) :
    TypedPayment PaymentState.Authorized :=
  { id := p.id
    orderId := p.orderId
    amount := p.amount
    currency := p.currency
    amount_pos := p.amount_pos }

/-- Capturing an authorized payment also creates the receipt needed to mark an order paid. -/
def capturePayment (p : TypedPayment PaymentState.Authorized) :
    TypedPayment PaymentState.Captured × CapturedPayment :=
  let captured : TypedPayment PaymentState.Captured :=
    { id := p.id
      orderId := p.orderId
      amount := p.amount
      currency := p.currency
      amount_pos := p.amount_pos }
  let receipt : CapturedPayment :=
    { orderId := p.orderId
      amount := p.amount
      currency := p.currency }
  (captured, receipt)

/-- Computes or checks `markPaid` using the validated data in this module. -/
def markPaid
    (order : TypedOrder OrderStatus.New)
    (payment : CapturedPayment)
    (hOrder : payment.orderId = order.id)
    (hAmount : payment.amount = order.total)
    (hCurrency : payment.currency = order.currency) :
    TypedOrder OrderStatus.Paid :=
  { id := order.id
    total := order.total
    currency := order.currency
    total_pos := order.total_pos }

/-- Tracks cumulative refunds and prevents refunding more than was captured. -/
structure PaymentLedger where
  captured : Money
  refunded : Money
  refunded_le_captured : refunded ≤ captured

/-- Computes or checks `remainingRefundAmount` using the validated data in this module. -/
def remainingRefundAmount (ledger : PaymentLedger) : Money :=
  ledger.captured - ledger.refunded

/-- Computes or checks `canRefund` using the validated data in this module. -/
def canRefund (ledger : PaymentLedger) (amount : Money) : Prop :=
  ledger.refunded + amount ≤ ledger.captured

/-- Computes or checks `issueRefund` using the validated data in this module. -/
def issueRefund (ledger : PaymentLedger) (amount : Money) (h : canRefund ledger amount) :
    PaymentLedger :=
  { captured := ledger.captured
    refunded := ledger.refunded + amount
    refunded_le_captured := h }

/-- States the safety property captured by `issueRefund_preserves_safety`. -/
theorem issueRefund_preserves_safety
    (ledger : PaymentLedger) (amount : Money) (h : canRefund ledger amount) :
    (issueRefund ledger amount h).refunded ≤ (issueRefund ledger amount h).captured := by
  exact (issueRefund ledger amount h).refunded_le_captured


end WebShopTheoryComplete
