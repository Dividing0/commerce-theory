import CommerceTheory.EventSourcing

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

end CommerceTheory.Tests
