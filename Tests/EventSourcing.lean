import CommerceTheory.EventSourcing
import CommerceTheory.OrderEventReplay

namespace CommerceTheory.Tests

def eventSourcingSku : Sku :=
  { value := 6101 }

def eventSourcingStock : StockState :=
  { sku := eventSourcingSku
    total := 10
    reserved := 3
    reserved_le_total := by norm_num }

def eventSourcingLedger : PaymentLedger :=
  { captured := 100
    refunded := 20
    refunded_le_captured := by norm_num }

def eventSourcingState : ValidSystemState :=
  { stock := eventSourcingStock
    ledger := eventSourcingLedger
    taxLiability := 11
    crmEventCount := 2
    logisticsEventCount := 5 }

def eventReplayAppliesAcceptedEvents : Bool :=
  let events :=
    [ DomainEvent.PaymentCaptured { value := 1 } 50,
      DomainEvent.RefundIssued { value := 1 } 30,
      DomainEvent.StockReserved eventSourcingSku 2,
      DomainEvent.TaxLiabilityRecorded 9 4,
      DomainEvent.LeadConverted { value := 7 } { value := 8 },
      DomainEvent.ShipmentDelivered { value := 12 } ]
  match replayDomainEvents? eventSourcingState events with
  | some next =>
      next.stock.reserved == 5 &&
        next.stock.total == 10 &&
        next.ledger.captured == 150 &&
        next.ledger.refunded == 50 &&
        next.taxLiability == 15 &&
        next.crmEventCount == 3 &&
        next.logisticsEventCount == 6
  | none => false

def eventReplayRejectsOversizedRefund : Bool :=
  match replayDomainEvents?
      eventSourcingState
      [DomainEvent.RefundIssued { value := 1 } 200] with
  | none => true
  | some _ => false

def idempotentEventAppliesOnlyOnce : Bool :=
  let key : IdempotencyKey := { value := 77 }
  let event := DomainEvent.PaymentCaptured { value := 1 } 25
  let idempotency : IdempotencyState := { processed := [] }
  match applyIdempotentDomainEvent? key event eventSourcingState idempotency with
  | some (afterFirst, afterFirstIdempotency) =>
      match applyIdempotentDomainEvent? key event afterFirst afterFirstIdempotency with
      | some (afterSecond, afterSecondIdempotency) =>
          afterFirst.ledger.captured == 125 &&
            afterSecond.ledger.captured == 125 &&
            afterSecondIdempotency.processed.length == 1
      | none => false
  | none => false

/-- info: true -/
#guard_msgs in
#eval eventReplayAppliesAcceptedEvents

/-- info: true -/
#guard_msgs in
#eval eventReplayRejectsOversizedRefund

/-- info: true -/
#guard_msgs in
#eval idempotentEventAppliesOnlyOnce

/-- A fresh order-aware projection has no registered payment authority. -/
def orderAwareInitial : OrderAwareSystemState :=
  initialOrderAwareSystemState eventSourcingStock

def twoOrderPaymentEvents : List DomainEvent :=
  [ .OrderPlaced { value := 1 } 50
  , .OrderPlaced { value := 2 } 200
  , .PaymentCaptured { value := 1 } 50
  , .PaymentCaptured { value := 2 } 200 ]

/-- An order cannot borrow the other order's captured funds for a refund. -/
def crossOrderRefundRejected : Bool :=
  match replayOrderAwareDomainEvents? orderAwareInitial twoOrderPaymentEvents with
  | none => false
  | some state =>
      (applyDomainEvent? state.system (.RefundIssued { value := 1 } 51)).isSome &&
        (applyOrderAwareDomainEvent? state (.RefundIssued { value := 1 } 51)).isNone

/-- Refunding one order changes precisely its own ledger and the reporting aggregate. -/
def orderRefundBalancesPass : Bool :=
  match replayOrderAwareDomainEvents? orderAwareInitial
      (twoOrderPaymentEvents ++ [.RefundIssued { value := 1 } 30]) with
  | none => false
  | some state =>
      match state.payments { value := 1 }, state.payments { value := 2 } with
      | some first, some second =>
          first.captured == 50 && first.refunded == 30 &&
            second.captured == 200 && second.refunded == 0 &&
            state.system.ledger.captured == 250 && state.system.ledger.refunded == 30 &&
            (applyOrderAwareDomainEvent? state (.RefundIssued { value := 1 } 21)).isNone &&
            (applyOrderAwareDomainEvent? state (.RefundIssued { value := 1 } 20)).isSome
      | _, _ => false

def unknownOrderPaymentRejected : Bool :=
  (applyOrderAwareDomainEvent? orderAwareInitial (.PaymentCaptured { value := 3 } 100)).isNone &&
    (applyOrderAwareDomainEvent? orderAwareInitial (.RefundIssued { value := 3 } 0)).isNone

/-- Placing an existing order again must not reset its captured or refunded balance. -/
def duplicateOrderPlacementRejected : Bool :=
  match replayOrderAwareDomainEvents? orderAwareInitial twoOrderPaymentEvents with
  | none => false
  | some state =>
      (applyOrderAwareDomainEvent? state (.OrderPlaced { value := 1 } 50)).isNone

def orderAwareInitialSnapshot : OrderAwareEventSnapshot :=
  { state := orderAwareInitial, lastSequence := 10 }

def sequencedOrderPaymentEvents : List EventEnvelope :=
  [ { sequence := 11, event := .OrderPlaced { value := 1 } 50 }
  , { sequence := 13, event := .PaymentCaptured { value := 1 } 50 }
  , { sequence := 20, event := .RefundIssued { value := 1 } 30 } ]

/-- Sequence gaps are accepted, and the last accepted envelope becomes the cursor. -/
def sequencedOrderReplayPass : Bool :=
  match replayOrderAwareFromSnapshot? orderAwareInitialSnapshot sequencedOrderPaymentEvents with
  | none => false
  | some snapshot =>
      match snapshot.state.payments { value := 1 } with
      | none => false
      | some ledger =>
          snapshot.lastSequence == 20 && ledger.captured == 50 && ledger.refunded == 30

def snapshotRejectsStaleDuplicateAndUnordered : Bool :=
  let placed := DomainEvent.OrderPlaced { value := 1 } 50
  let captured := DomainEvent.PaymentCaptured { value := 1 } 50
  (replayOrderAwareFromSnapshot? orderAwareInitialSnapshot
    [{ sequence := 9, event := placed }]).isNone &&
  (replayOrderAwareFromSnapshot? orderAwareInitialSnapshot
    [{ sequence := 10, event := placed }]).isNone &&
  (replayOrderAwareFromSnapshot? orderAwareInitialSnapshot
    [{ sequence := 11, event := placed }, { sequence := 11, event := captured }]).isNone &&
  (replayOrderAwareFromSnapshot? orderAwareInitialSnapshot
    [{ sequence := 12, event := placed }, { sequence := 11, event := captured }]).isNone

/-- Resumption retains the order ledger and rejects already-applied envelopes. -/
def snapshotResumptionPass : Bool :=
  match replayOrderAwareFromSnapshot? orderAwareInitialSnapshot
      (sequencedOrderPaymentEvents.take 2) with
  | none => false
  | some prefixSnapshot =>
      (replayOrderAwareFromSnapshot? prefixSnapshot
        [{ sequence := 13, event := .PaymentCaptured { value := 1 } 50 }]).isNone &&
      match replayOrderAwareFromSnapshot? prefixSnapshot (sequencedOrderPaymentEvents.drop 2) with
      | none => false
      | some after =>
          match after.state.payments { value := 1 } with
          | none => false
          | some ledger => after.lastSequence == 20 && ledger.refunded == 30

/-- New sequences cannot make invalid event payloads acceptable. -/
def sequencedInvalidPayloadRejected : Bool :=
  (replayOrderAwareFromSnapshot? orderAwareInitialSnapshot
    [{ sequence := 11, event := .PaymentCaptured { value := 1 } 50 }]).isNone &&
  (replayOrderAwareFromSnapshot? orderAwareInitialSnapshot
    (sequencedOrderPaymentEvents ++
      [{ sequence := 21, event := .RefundIssued { value := 1 } 21 }])).isNone &&
  (replayFromSnapshot? { state := eventSourcingState, lastSequence := 10 }
    [{ sequence := 11, event := .StockReserved eventSourcingSku 100 }]).isNone

def aggregateSnapshotChecksSequence : Bool :=
  let snapshot : EventSnapshot := { state := eventSourcingState, lastSequence := 10 }
  (replayFromSnapshot? snapshot
    [{ sequence := 10, event := .PaymentCaptured { value := 1 } 50 }]).isNone &&
  match replayFromSnapshot? snapshot
      [{ sequence := 12, event := .PaymentCaptured { value := 1 } 50 }] with
  | none => false
  | some next => next.lastSequence == 12 && next.state.ledger.captured == 150

example : replayOrderAwareFromSnapshot? orderAwareInitialSnapshot [] =
    some orderAwareInitialSnapshot := by rfl

example : replayFromSnapshot? { state := eventSourcingState, lastSequence := 10 } [] =
    some { state := eventSourcingState, lastSequence := 10 } := by rfl

/-- info: true -/
#guard_msgs in
#eval crossOrderRefundRejected

/-- info: true -/
#guard_msgs in
#eval orderRefundBalancesPass

/-- info: true -/
#guard_msgs in
#eval unknownOrderPaymentRejected

/-- info: true -/
#guard_msgs in
#eval duplicateOrderPlacementRejected

/-- info: true -/
#guard_msgs in
#eval sequencedOrderReplayPass

/-- info: true -/
#guard_msgs in
#eval snapshotRejectsStaleDuplicateAndUnordered

/-- info: true -/
#guard_msgs in
#eval snapshotResumptionPass

/-- info: true -/
#guard_msgs in
#eval sequencedInvalidPayloadRejected

/-- info: true -/
#guard_msgs in
#eval aggregateSnapshotChecksSequence

end CommerceTheory.Tests
