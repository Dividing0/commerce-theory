import CommerceTheory.EventSourcing
import Cslib.Computability.Languages.RegularLanguage

namespace CommerceTheory

/-! ## CSLib automata for domain-event languages -/

/-!
This module uses CSLib deterministic finite acceptors to model coarse event
sequence validity.  It gives event-sourcing rules a regular-language interface
that can later be composed with CSLib closure theorems.
-/

/-- Abstract event symbols for lifecycle validation. -/
inductive OrderEventSymbol where
  | OrderPlaced
  | PaymentCaptured
  | RefundIssued
  | StockReserved
  | OrderShipped
  | Other
deriving DecidableEq, Repr

/-- Coarse lifecycle state used by the event-sequence validator. -/
inductive OrderEventValidationState where
  | Start
  | Placed
  | Captured
  | Refunded
  | Shipped
  | Invalid
deriving DecidableEq, Repr, Fintype

/-- Forget event payloads and keep only the lifecycle symbol. -/
def domainEventSymbol : DomainEvent → OrderEventSymbol
  | DomainEvent.OrderPlaced _ _ => OrderEventSymbol.OrderPlaced
  | DomainEvent.PaymentCaptured _ _ => OrderEventSymbol.PaymentCaptured
  | DomainEvent.RefundIssued _ _ => OrderEventSymbol.RefundIssued
  | DomainEvent.StockReserved _ _ => OrderEventSymbol.StockReserved
  | DomainEvent.OrderShipped _ => OrderEventSymbol.OrderShipped
  | DomainEvent.LeadConverted _ _ => OrderEventSymbol.Other
  | DomainEvent.SupportCaseOpened _ _ => OrderEventSymbol.Other
  | DomainEvent.ShipmentPlanned _ _ => OrderEventSymbol.Other
  | DomainEvent.ShipmentDelivered _ => OrderEventSymbol.Other
  | DomainEvent.ReturnApproved _ _ _ => OrderEventSymbol.Other

/-- Convert a concrete event stream into the word read by the validator. -/
def domainEventSymbols (events : List DomainEvent) : List OrderEventSymbol :=
  events.map domainEventSymbol

/-- Transition function for a conservative order-event lifecycle validator. -/
def orderEventValidationStep :
    OrderEventValidationState → OrderEventSymbol → OrderEventValidationState
  | OrderEventValidationState.Start, OrderEventSymbol.OrderPlaced =>
      OrderEventValidationState.Placed
  | OrderEventValidationState.Placed, OrderEventSymbol.StockReserved =>
      OrderEventValidationState.Placed
  | OrderEventValidationState.Placed, OrderEventSymbol.PaymentCaptured =>
      OrderEventValidationState.Captured
  | OrderEventValidationState.Captured, OrderEventSymbol.StockReserved =>
      OrderEventValidationState.Captured
  | OrderEventValidationState.Captured, OrderEventSymbol.RefundIssued =>
      OrderEventValidationState.Refunded
  | OrderEventValidationState.Captured, OrderEventSymbol.OrderShipped =>
      OrderEventValidationState.Shipped
  | state, OrderEventSymbol.Other =>
      state
  | _, _ =>
      OrderEventValidationState.Invalid

/-- CSLib deterministic finite acceptor for valid order-event words. -/
def orderEventValidator :
    Cslib.Automata.DA.FinAcc OrderEventValidationState OrderEventSymbol where
  tr := orderEventValidationStep
  start := OrderEventValidationState.Start
  accept := { state | state ≠ OrderEventValidationState.Invalid }

/-- A normal place/capture/ship word is accepted. -/
theorem paidShipEventWord_accepted :
    orderEventValidator.mtr orderEventValidator.start
      [ OrderEventSymbol.OrderPlaced
      , OrderEventSymbol.PaymentCaptured
      , OrderEventSymbol.OrderShipped
      ] ∈ orderEventValidator.accept := by
  simp [orderEventValidator, orderEventValidationStep, Cslib.FLTS.mtr]

/-- Refund before capture is rejected by the automaton. -/
theorem refundBeforeCapture_rejected :
    orderEventValidator.mtr orderEventValidator.start
      [OrderEventSymbol.OrderPlaced, OrderEventSymbol.RefundIssued] =
        OrderEventValidationState.Invalid := by
  native_decide

/-- Shipment before capture is rejected by the automaton. -/
theorem shipBeforeCapture_rejected :
    orderEventValidator.mtr orderEventValidator.start
      [OrderEventSymbol.OrderPlaced, OrderEventSymbol.OrderShipped] =
        OrderEventValidationState.Invalid := by
  native_decide

/-- The language accepted by the validator is regular by CSLib's DFA characterization. -/
theorem orderEventValidator_language_regular :
    (Cslib.Automata.Acceptor.language orderEventValidator).IsRegular := by
  rw [Cslib.Language.IsRegular.iff_dfa]
  exact ⟨OrderEventValidationState, inferInstance, orderEventValidator, rfl⟩

end CommerceTheory
