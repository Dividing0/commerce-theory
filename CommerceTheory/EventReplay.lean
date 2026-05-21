import CommerceTheory.EventSourcing
import Cslib.Foundations.Data.RelatesInSteps

namespace CommerceTheory

/-! ## CSLib bounded event replay -/

/-!
CSLib's `Relation.RelatesInSteps` gives event sourcing a reusable step-counted
semantics.  The definitions below keep the existing validated event appliers,
but expose them as one-step relations that can be composed exactly or within a
step bound.
-/

/-- One accepted webhook advances the ordering cursor to a newer sequence. -/
inductive WebhookOrderingStep : WebhookOrderingState → WebhookOrderingState → Prop where
  | accept
      (state : WebhookOrderingState) (sequence : Nat)
      (h : state.lastSequence < sequence) :
      WebhookOrderingStep state (applyWebhook state sequence h)

/-- Webhook replay in exactly `n` accepted ordering steps. -/
abbrev WebhookReplayInSteps :=
  Relation.RelatesInSteps WebhookOrderingStep

/-- Webhook replay in at most `n` accepted ordering steps. -/
abbrev WebhookReplayWithinSteps :=
  Relation.RelatesWithinSteps WebhookOrderingStep

/-- One accepted webhook strictly increases the recorded sequence. -/
theorem webhookOrderingStep_increases
    {before after : WebhookOrderingState}
    (h : WebhookOrderingStep before after) :
    before.lastSequence < after.lastSequence := by
  cases h with
  | accept sequence hseq =>
      simpa [applyWebhook] using hseq

/-- Any bounded webhook replay leaves the sequence monotone. -/
theorem webhookReplayInSteps_sequence_monotone
    {before after : WebhookOrderingState} {steps : Nat}
    (h : WebhookReplayInSteps before after steps) :
    before.lastSequence ≤ after.lastSequence := by
  induction h using Relation.RelatesInSteps.head_induction_on with
  | hrefl =>
      exact Nat.le_refl after.lastSequence
  | hhead hstep _ ih =>
      exact (Nat.le_of_lt (webhookOrderingStep_increases hstep)).trans ih

/-- The same monotonicity guarantee for replay within a step bound. -/
theorem webhookReplayWithinSteps_sequence_monotone
    {before after : WebhookOrderingState} {bound : Nat}
    (h : WebhookReplayWithinSteps before after bound) :
    before.lastSequence ≤ after.lastSequence := by
  rcases h with ⟨steps, _hsteps_le_bound, hsteps⟩
  exact webhookReplayInSteps_sequence_monotone hsteps

/-- Strictly ordered webhook lists induce a CSLib replay with matching step count. -/
theorem orderedWebhookStream_relatesInSteps
    (state : WebhookOrderingState) (events : List EventEnvelope)
    (h : streamSequencesStrictlyIncreaseFrom state.lastSequence events) :
    ∃ next : WebhookOrderingState,
      WebhookReplayInSteps state next events.length := by
  induction events generalizing state with
  | nil =>
      exact ⟨state, Relation.RelatesInSteps.refl state⟩
  | cons event rest ih =>
      have hseq : state.lastSequence < event.sequence := h.left
      let afterHead := applyWebhook state event.sequence hseq
      have hrest :
          streamSequencesStrictlyIncreaseFrom afterHead.lastSequence rest := by
        simpa [afterHead, applyWebhook] using h.right
      rcases ih afterHead hrest with ⟨final, hfinal⟩
      refine ⟨final, ?_⟩
      exact Relation.RelatesInSteps.head
        state afterHead final rest.length
        (WebhookOrderingStep.accept state event.sequence hseq)
        hfinal

/-- One validated state event transforms a valid system state into another. -/
inductive ValidSystemEventStep : ValidSystemState → ValidSystemState → Prop where
  | stockReserved
      (state : ValidSystemState) (sku : Sku) (quantity : Quantity)
      (hSku : state.stock.sku = sku)
      (hReserve : canReserve state.stock quantity) :
      ValidSystemEventStep state
        (applyStockReservedEvent state sku quantity hSku hReserve)
  | refundIssued
      (state : ValidSystemState) (amount : Money)
      (hRefund : canRefund state.ledger amount) :
      ValidSystemEventStep state
        (applyRefundIssuedEvent state amount hRefund)
  | reservationReleased
      (state : ValidSystemState) (sku : Sku) (quantity : Quantity)
      (hSku : state.stock.sku = sku)
      (hReserved : quantity ≤ state.stock.reserved) :
      ValidSystemEventStep state
        (applyReservationReleasedEvent state sku quantity hSku hReserved)
  | reservedShipmentConfirmed
      (state : ValidSystemState) (sku : Sku) (quantity : Quantity)
      (hSku : state.stock.sku = sku)
      (hReserved : quantity ≤ state.stock.reserved) :
      ValidSystemEventStep state
        (applyReservedShipmentConfirmedEvent state sku quantity hSku hReserved)
  | taxLiabilityRecorded
      (state : ValidSystemState) (amount : Money) :
      ValidSystemEventStep state
        (applyTaxLiabilityRecordedEvent state amount)
  | crmProjected
      (state : ValidSystemState) :
      ValidSystemEventStep state
        (applyCRMProjectedEvent state)
  | logisticsProjected
      (state : ValidSystemState) :
      ValidSystemEventStep state
        (applyLogisticsProjectedEvent state)

/-- Valid system replay in exactly `n` accepted state-event steps. -/
abbrev ValidSystemReplayInSteps :=
  Relation.RelatesInSteps ValidSystemEventStep

/-- Valid system replay in at most `n` accepted state-event steps. -/
abbrev ValidSystemReplayWithinSteps :=
  Relation.RelatesWithinSteps ValidSystemEventStep

/-- A single valid system event preserves stock and ledger validity. -/
theorem validSystemEventStep_preserves_validity
    {before after : ValidSystemState}
    (h : ValidSystemEventStep before after) :
    after.stock.reserved ≤ after.stock.total ∧
      after.ledger.refunded ≤ after.ledger.captured := by
  cases h with
  | stockReserved sku quantity hSku hReserve =>
      exact applyStockReservedEvent_preserves_validity before sku quantity hSku hReserve
  | refundIssued amount hRefund =>
      exact applyRefundIssuedEvent_preserves_validity before amount hRefund
  | reservationReleased sku quantity hSku hReserved =>
      exact applyReservationReleasedEvent_preserves_validity
        before sku quantity hSku hReserved
  | reservedShipmentConfirmed sku quantity hSku hReserved =>
      exact applyReservedShipmentConfirmedEvent_preserves_validity
        before sku quantity hSku hReserved
  | taxLiabilityRecorded amount =>
      exact applyTaxLiabilityRecordedEvent_preserves_validity before amount
  | crmProjected =>
      exact applyCRMProjectedEvent_preserves_validity before
  | logisticsProjected =>
      exact applyLogisticsProjectedEvent_preserves_validity before

/-- Event-aware valid-system projection step for core, CRM, and logistics events. -/
inductive ValidDomainEventStep :
    DomainEvent → ValidSystemState → ValidSystemState → Prop where
  | stockReserved
      (state : ValidSystemState) (sku : Sku) (quantity : Quantity)
      (hSku : state.stock.sku = sku)
      (hReserve : canReserve state.stock quantity) :
      ValidDomainEventStep (DomainEvent.StockReserved sku quantity) state
        (applyStockReservedEvent state sku quantity hSku hReserve)
  | refundIssued
      (state : ValidSystemState) (orderId : OrderId) (amount : Money)
      (hRefund : canRefund state.ledger amount) :
      ValidDomainEventStep (DomainEvent.RefundIssued orderId amount) state
        (applyRefundIssuedEvent state amount hRefund)
  | reservationReleased
      (state : ValidSystemState) (sku : Sku) (quantity : Quantity)
      (hSku : state.stock.sku = sku)
      (hReserved : quantity ≤ state.stock.reserved) :
      ValidDomainEventStep (DomainEvent.ReservationReleased sku quantity) state
        (applyReservationReleasedEvent state sku quantity hSku hReserved)
  | reservedShipmentConfirmed
      (state : ValidSystemState) (sku : Sku) (quantity : Quantity)
      (hSku : state.stock.sku = sku)
      (hReserved : quantity ≤ state.stock.reserved) :
      ValidDomainEventStep
        (DomainEvent.ReservedShipmentConfirmed sku quantity) state
        (applyReservedShipmentConfirmedEvent state sku quantity hSku hReserved)
  | taxLiabilityRecorded
      (state : ValidSystemState) (id : Id) (amount : Money) :
      ValidDomainEventStep (DomainEvent.TaxLiabilityRecorded id amount) state
        (applyTaxLiabilityRecordedEvent state amount)
  | crmProjected
      (event : DomainEvent) (state : ValidSystemState)
      (hCRM : domainEventIsCRM event) :
      ValidDomainEventStep event state (applyCRMProjectedEvent state)
  | logisticsProjected
      (event : DomainEvent) (state : ValidSystemState)
      (hLogistics : domainEventIsLogistics event) :
      ValidDomainEventStep event state (applyLogisticsProjectedEvent state)

/-- Event-aware projection steps preserve stock and ledger validity. -/
theorem validDomainEventStep_preserves_validity
    {event : DomainEvent} {before after : ValidSystemState}
    (h : ValidDomainEventStep event before after) :
    after.stock.reserved ≤ after.stock.total ∧
      after.ledger.refunded ≤ after.ledger.captured := by
  cases h with
  | stockReserved =>
      exact ⟨after.stock.reserved_le_total, after.ledger.refunded_le_captured⟩
  | refundIssued =>
      exact ⟨after.stock.reserved_le_total, after.ledger.refunded_le_captured⟩
  | reservationReleased =>
      exact ⟨after.stock.reserved_le_total, after.ledger.refunded_le_captured⟩
  | reservedShipmentConfirmed =>
      exact ⟨after.stock.reserved_le_total, after.ledger.refunded_le_captured⟩
  | taxLiabilityRecorded =>
      exact ⟨after.stock.reserved_le_total, after.ledger.refunded_le_captured⟩
  | crmProjected =>
      exact ⟨after.stock.reserved_le_total, after.ledger.refunded_le_captured⟩
  | logisticsProjected =>
      exact ⟨after.stock.reserved_le_total, after.ledger.refunded_le_captured⟩

/-- Any exact-step valid system replay preserves stock and ledger validity. -/
theorem validSystemReplayInSteps_preserves_validity
    {before after : ValidSystemState} {steps : Nat}
    (h : ValidSystemReplayInSteps before after steps) :
    after.stock.reserved ≤ after.stock.total ∧
      after.ledger.refunded ≤ after.ledger.captured := by
  induction h using Relation.RelatesInSteps.head_induction_on with
  | hrefl =>
      exact ⟨after.stock.reserved_le_total, after.ledger.refunded_le_captured⟩
  | hhead _ _ ih =>
      exact ih

/-- Any bounded valid system replay preserves stock and ledger validity. -/
theorem validSystemReplayWithinSteps_preserves_validity
    {before after : ValidSystemState} {bound : Nat}
    (h : ValidSystemReplayWithinSteps before after bound) :
    after.stock.reserved ≤ after.stock.total ∧
      after.ledger.refunded ≤ after.ledger.captured := by
  rcases h with ⟨steps, _hsteps_le_bound, hsteps⟩
  exact validSystemReplayInSteps_preserves_validity hsteps

/-- A representative two-step replay: reserve stock, then issue a valid refund. -/
theorem reserve_then_refund_replay_in_two_steps
    (state : ValidSystemState)
    (sku : Sku) (quantity refundAmount : Nat)
    (hSku : state.stock.sku = sku)
    (hReserve : canReserve state.stock quantity)
    (hRefund : canRefund state.ledger refundAmount) :
    let afterReserve := applyStockReservedEvent state sku quantity hSku hReserve
    let afterRefund := applyRefundIssuedEvent afterReserve refundAmount hRefund
    ValidSystemReplayInSteps state afterRefund 2 := by
  intro afterReserve afterRefund
  exact Relation.RelatesInSteps.tail
    state afterReserve afterRefund 1
    (Relation.RelatesInSteps.single
      (ValidSystemEventStep.stockReserved state sku quantity hSku hReserve))
    (ValidSystemEventStep.refundIssued afterReserve refundAmount hRefund)

end CommerceTheory
