import CommerceTheory.Orders
import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.Termination
import Cslib.Foundations.Semantics.LTS.TraceEq

namespace CommerceTheory

/-! ## CSLib-backed order workflow semantics -/

/-!
The existing order status relation is useful as a local business rule. CSLib's
labelled transition systems add reusable computer-science structure around that
relation: labelled traces, multistep reachability, terminal-state checks, and
trace equivalence for lifecycle states.
-/

/-- Business labels for the allowed order-status transitions. -/
inductive OrderTransitionLabel where
  | CapturePayment
  | CancelBeforePayment
  | MarkBackordered
  | PackPaidOrder
  | RefundPaidOrder
  | ShipPackedOrder
  | ConfirmDelivery
  | RefundDeliveredOrder
  | ReceiveBackorderPayment
  | CancelBackorder
deriving DecidableEq, Repr

/-- The order status machine as a CSLib labelled transition system. -/
def orderStatusLTS : Cslib.LTS OrderStatus OrderTransitionLabel where
  Tr := fun source label target =>
    match label with
    | OrderTransitionLabel.CapturePayment =>
        source = OrderStatus.New ∧ target = OrderStatus.Paid
    | OrderTransitionLabel.CancelBeforePayment =>
        source = OrderStatus.New ∧ target = OrderStatus.Cancelled
    | OrderTransitionLabel.MarkBackordered =>
        source = OrderStatus.New ∧ target = OrderStatus.Backordered
    | OrderTransitionLabel.PackPaidOrder =>
        source = OrderStatus.Paid ∧ target = OrderStatus.Packed
    | OrderTransitionLabel.RefundPaidOrder =>
        source = OrderStatus.Paid ∧ target = OrderStatus.Refunded
    | OrderTransitionLabel.ShipPackedOrder =>
        source = OrderStatus.Packed ∧ target = OrderStatus.Shipped
    | OrderTransitionLabel.ConfirmDelivery =>
        source = OrderStatus.Shipped ∧ target = OrderStatus.Delivered
    | OrderTransitionLabel.RefundDeliveredOrder =>
        source = OrderStatus.Delivered ∧ target = OrderStatus.Refunded
    | OrderTransitionLabel.ReceiveBackorderPayment =>
        source = OrderStatus.Backordered ∧ target = OrderStatus.Paid
    | OrderTransitionLabel.CancelBackorder =>
        source = OrderStatus.Backordered ∧ target = OrderStatus.Cancelled

/-- Every CSLib-labelled transition is one of the existing business transitions. -/
theorem orderStatusLTS_transition_allowed
    {source target : OrderStatus} {label : OrderTransitionLabel}
    (h : orderStatusLTS.Tr source label target) :
    CanOrderTransition source target := by
  cases label <;> simp [orderStatusLTS] at h <;> rcases h with ⟨rfl, rfl⟩
  all_goals constructor

/-- Every existing business transition has a matching CSLib transition label. -/
theorem order_transition_has_lts_label
    {source target : OrderStatus} (h : CanOrderTransition source target) :
    ∃ label : OrderTransitionLabel, orderStatusLTS.Tr source label target := by
  cases h with
  | new_paid =>
      exact ⟨OrderTransitionLabel.CapturePayment, by simp [orderStatusLTS]⟩
  | new_cancelled =>
      exact ⟨OrderTransitionLabel.CancelBeforePayment, by simp [orderStatusLTS]⟩
  | new_backordered =>
      exact ⟨OrderTransitionLabel.MarkBackordered, by simp [orderStatusLTS]⟩
  | paid_packed =>
      exact ⟨OrderTransitionLabel.PackPaidOrder, by simp [orderStatusLTS]⟩
  | paid_refunded =>
      exact ⟨OrderTransitionLabel.RefundPaidOrder, by simp [orderStatusLTS]⟩
  | packed_shipped =>
      exact ⟨OrderTransitionLabel.ShipPackedOrder, by simp [orderStatusLTS]⟩
  | shipped_delivered =>
      exact ⟨OrderTransitionLabel.ConfirmDelivery, by simp [orderStatusLTS]⟩
  | delivered_refunded =>
      exact ⟨OrderTransitionLabel.RefundDeliveredOrder, by simp [orderStatusLTS]⟩
  | backordered_paid =>
      exact ⟨OrderTransitionLabel.ReceiveBackorderPayment, by simp [orderStatusLTS]⟩
  | backordered_cancelled =>
      exact ⟨OrderTransitionLabel.CancelBackorder, by simp [orderStatusLTS]⟩

/-- Normal paid fulfillment trace from a new order to delivery. -/
def paidFulfillmentTrace : List OrderTransitionLabel :=
  [ OrderTransitionLabel.CapturePayment
  , OrderTransitionLabel.PackPaidOrder
  , OrderTransitionLabel.ShipPackedOrder
  , OrderTransitionLabel.ConfirmDelivery
  ]

/-- CSLib proves the full paid-fulfillment trace as a multistep transition. -/
theorem paidFulfillmentTrace_reaches_delivered :
    orderStatusLTS.MTr OrderStatus.New paidFulfillmentTrace OrderStatus.Delivered := by
  unfold paidFulfillmentTrace
  refine Cslib.LTS.MTr.stepL (s2 := OrderStatus.Paid) ?_ ?_
  · simp [orderStatusLTS]
  · refine Cslib.LTS.MTr.stepL (s2 := OrderStatus.Packed) ?_ ?_
    · simp [orderStatusLTS]
    · refine Cslib.LTS.MTr.stepL (s2 := OrderStatus.Shipped) ?_ ?_
      · simp [orderStatusLTS]
      · refine Cslib.LTS.MTr.stepL (s2 := OrderStatus.Delivered) ?_ ?_
        · simp [orderStatusLTS]
        · exact Cslib.LTS.MTr.refl

/-- A new order can reach delivered through the paid-fulfillment trace. -/
theorem new_order_can_reach_delivered :
    orderStatusLTS.CanReach OrderStatus.New OrderStatus.Delivered := by
  exact ⟨paidFulfillmentTrace, paidFulfillmentTrace_reaches_delivered⟩

/-- A cancellation trace for an order that has not been paid. -/
def unpaidCancellationTrace : List OrderTransitionLabel :=
  [OrderTransitionLabel.CancelBeforePayment]

/-- A new order can also reach cancelled when it is cancelled before payment. -/
theorem unpaidCancellationTrace_reaches_cancelled :
    orderStatusLTS.MTr OrderStatus.New unpaidCancellationTrace OrderStatus.Cancelled := by
  unfold unpaidCancellationTrace
  refine Cslib.LTS.MTr.stepL (s2 := OrderStatus.Cancelled) ?_ ?_
  · simp [orderStatusLTS]
  · exact Cslib.LTS.MTr.refl

/-- Fulfillment termination treats delivered, cancelled, and refunded as final outcomes. -/
def terminalOrderStatus : OrderStatus → Prop
  | OrderStatus.Delivered => True
  | OrderStatus.Cancelled => True
  | OrderStatus.Refunded => True
  | _ => False

/-- The normal paid-fulfillment path may terminate in a delivered order. -/
theorem new_order_may_terminate :
    Cslib.LTS.MayTerminate orderStatusLTS terminalOrderStatus OrderStatus.New := by
  exact ⟨OrderStatus.Delivered, trivial, new_order_can_reach_delivered⟩

/-- A new order is not stuck because payment capture is available. -/
theorem new_order_not_stuck :
    ¬ Cslib.LTS.Stuck orderStatusLTS terminalOrderStatus OrderStatus.New := by
  intro h
  exact h.right
    ⟨OrderTransitionLabel.CapturePayment, OrderStatus.Paid, by simp [orderStatusLTS]⟩

/-- Cancelled orders have no outgoing labelled transitions. -/
theorem cancelled_order_has_no_lts_outgoing
    (label : OrderTransitionLabel) (next : OrderStatus) :
    ¬ orderStatusLTS.Tr OrderStatus.Cancelled label next := by
  intro h
  cases label <;> cases next <;> simp [orderStatusLTS] at h

/-- Refunded orders have no outgoing labelled transitions. -/
theorem refunded_order_has_no_lts_outgoing
    (label : OrderTransitionLabel) (next : OrderStatus) :
    ¬ orderStatusLTS.Tr OrderStatus.Refunded label next := by
  intro h
  cases label <;> cases next <;> simp [orderStatusLTS] at h

/--
Cancelled and refunded orders expose the same future traces: only the empty trace.
This is a CSLib trace-equivalence statement over the order-status LTS.
-/
theorem cancelled_trace_equivalent_refunded :
    Cslib.LTS.HomTraceEq orderStatusLTS OrderStatus.Cancelled OrderStatus.Refunded := by
  unfold Cslib.LTS.HomTraceEq Cslib.LTS.TraceEq Cslib.LTS.traces
  ext trace
  constructor
  · intro h
    rcases h with ⟨final, htrace⟩
    cases htrace with
    | refl =>
        exact ⟨OrderStatus.Refunded, Cslib.LTS.MTr.refl⟩
    | stepL htr _ =>
        exact False.elim (cancelled_order_has_no_lts_outgoing _ _ htr)
  · intro h
    rcases h with ⟨final, htrace⟩
    cases htrace with
    | refl =>
        exact ⟨OrderStatus.Cancelled, Cslib.LTS.MTr.refl⟩
    | stepL htr _ =>
        exact False.elim (refunded_order_has_no_lts_outgoing _ _ htr)

end CommerceTheory
