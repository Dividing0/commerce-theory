import CommerceTheory.RiskPrivacy

namespace CommerceTheory

/-! ## 15. Event sourcing, idempotency, webhooks, and valid state preservation -/

/-!
Event-sourcing definitions describe envelopes, streams, webhook ordering, and
idempotency. The system-state theorem demonstrates the intended proof style:
operations should preserve global validity when their local invariants hold.
-/

/-- Closed set of cases for `DomainEvent` in the commerce domain model. -/
inductive DomainEvent where
  | OrderPlaced : OrderId → Money → DomainEvent
  | PaymentCaptured : OrderId → Money → DomainEvent
  | RefundIssued : OrderId → Money → DomainEvent
  | StockReserved : Sku → Quantity → DomainEvent
  | ReservationReleased : Sku → Quantity → DomainEvent
  | ReservedShipmentConfirmed : Sku → Quantity → DomainEvent
  | TaxLiabilityRecorded : Id → Money → DomainEvent
  | OrderShipped : OrderId → DomainEvent
  | LeadConverted : LeadId → OpportunityId → DomainEvent
  | SupportCaseOpened : SupportCaseId → Option OrderId → DomainEvent
  | ShipmentPlanned : ShipmentId → OrderId → DomainEvent
  | ShipmentDelivered : ShipmentId → DomainEvent
  | ReturnApproved : ReturnAuthorizationId → OrderId → Money → DomainEvent
deriving DecidableEq, Repr

/-- CRM events are the domain events projected into CRM read models. -/
def domainEventIsCRM : DomainEvent → Prop
  | DomainEvent.LeadConverted _ _ => True
  | DomainEvent.SupportCaseOpened _ _ => True
  | _ => False

/-- Logistics events are the domain events projected into logistics read models. -/
def domainEventIsLogistics : DomainEvent → Prop
  | DomainEvent.ShipmentPlanned _ _ => True
  | DomainEvent.ShipmentDelivered _ => True
  | DomainEvent.ReturnApproved _ _ _ => True
  | _ => False

/-- Data shape for `EventEnvelope`; proof fields record invariants when needed. -/
structure EventEnvelope where
  sequence : Nat
  event : DomainEvent

/-- Data shape for `EventStream`; proof fields record invariants when needed. -/
structure EventStream where
  events : List EventEnvelope
  lastSequence : Nat

/-- Event envelopes are strictly ordered after a supplied previous sequence. -/
def streamSequencesStrictlyIncreaseFrom : Nat → List EventEnvelope → Prop
  | _last, [] => True
  | last, event :: rest =>
      last < event.sequence ∧ streamSequencesStrictlyIncreaseFrom event.sequence rest

/-- Event streams whose envelopes are ordered from sequence zero. -/
def streamSequencesStrictlyIncrease (stream : EventStream) : Prop :=
  streamSequencesStrictlyIncreaseFrom 0 stream.events

/-- Ordered nonempty streams expose that the first envelope sequence is positive. -/
theorem streamSequencesStrictlyIncreaseFrom_head
    (last : Nat) (event : EventEnvelope) (rest : List EventEnvelope)
    (h : streamSequencesStrictlyIncreaseFrom last (event :: rest)) :
    last < event.sequence := by
  exact h.left


/-- Data shape for `WebhookOrderingState`; proof fields record invariants when needed. -/
structure WebhookOrderingState where
  lastSequence : Nat

/-- Computes or checks `applyWebhook` using the validated data in this module. -/
def applyWebhook
    (s : WebhookOrderingState) (seq : Nat) (_h : s.lastSequence < seq) : WebhookOrderingState :=
  { lastSequence := seq }

/-- States the safety property captured by `applyWebhook_increases_sequence`. -/
theorem applyWebhook_increases_sequence
    (s : WebhookOrderingState) (seq : Nat) (h : s.lastSequence < seq) :
    s.lastSequence < (applyWebhook s seq h).lastSequence := by
  exact h

/-- Applying an accepted webhook records the accepted sequence exactly. -/
theorem applyWebhook_sets_sequence
    (s : WebhookOrderingState) (seq : Nat) (h : s.lastSequence < seq) :
    (applyWebhook s seq h).lastSequence = seq := by
  rfl

/-- Replay a webhook stream, rejecting the first envelope that is not newer. -/
def replayWebhookStream :
    WebhookOrderingState → List EventEnvelope → Option WebhookOrderingState
  | s, [] => some s
  | s, event :: rest =>
      if h : s.lastSequence < event.sequence then
        replayWebhookStream (applyWebhook s event.sequence h) rest
      else
        none

/-- Strictly ordered webhook streams replay successfully. -/
theorem replayWebhookStream_succeeds_of_ordered
    (s : WebhookOrderingState) (events : List EventEnvelope)
    (h : streamSequencesStrictlyIncreaseFrom s.lastSequence events) :
    ∃ next : WebhookOrderingState, replayWebhookStream s events = some next := by
  induction events generalizing s with
  | nil =>
      exact ⟨s, rfl⟩
  | cons event rest ih =>
      have hseq : s.lastSequence < event.sequence := h.left
      have hrest :
          streamSequencesStrictlyIncreaseFrom
            (applyWebhook s event.sequence hseq).lastSequence rest := by
        simpa [applyWebhook] using h.right
      rcases ih (applyWebhook s event.sequence hseq) hrest with ⟨next, hnext⟩
      refine ⟨next, ?_⟩
      simp [replayWebhookStream, hseq, hnext]

/-- Data shape for `IdempotencyState`; proof fields record invariants when needed. -/
structure IdempotencyState where
  processed : List IdempotencyKey

/-- Computes or checks `alreadyProcessed` using the validated data in this module. -/
def alreadyProcessed (key : IdempotencyKey) (s : IdempotencyState) : Prop :=
  key ∈ s.processed

instance instDecidableAlreadyProcessed (key : IdempotencyKey) (s : IdempotencyState) :
    Decidable (alreadyProcessed key s) := by
  unfold alreadyProcessed
  infer_instance

/-- Computes or checks `markProcessed` using the validated data in this module. -/
def markProcessed (key : IdempotencyKey) (s : IdempotencyState) : IdempotencyState :=
  { processed := key :: s.processed }

/-- States the safety property captured by `markProcessed_contains_key`. -/
theorem markProcessed_contains_key (key : IdempotencyKey) (s : IdempotencyState) :
    alreadyProcessed key (markProcessed key s) := by
  unfold alreadyProcessed markProcessed
  simp

/-- Marking a new key keeps every previously processed key. -/
theorem markProcessed_preserves_existing
    (key existing : IdempotencyKey) (s : IdempotencyState)
    (h : alreadyProcessed existing s) :
    alreadyProcessed existing (markProcessed key s) := by
  unfold alreadyProcessed markProcessed at *
  simp [h]

/-- The processed set after marking is exactly the new key plus the old set. -/
theorem alreadyProcessed_markProcessed_iff
    (key existing : IdempotencyKey) (s : IdempotencyState) :
    alreadyProcessed existing (markProcessed key s) ↔
      existing = key ∨ alreadyProcessed existing s := by
  unfold alreadyProcessed markProcessed
  simp

/-- Data shape for `ValidSystemState`; proof fields record invariants when needed. -/
structure ValidSystemState where
  stock : StockState
  ledger : PaymentLedger
  taxLiability : Money
  crmEventCount : Nat
  logisticsEventCount : Nat

/-- Apply a stock-reserved event to the validated state when SKU and quantity are valid. -/
def applyStockReservedEvent
    (state : ValidSystemState)
    (sku : Sku) (quantity : Quantity)
    (_hSku : state.stock.sku = sku)
    (hReserve : canReserve state.stock quantity) :
    ValidSystemState :=
  { stock := reserveStock state.stock quantity hReserve
    ledger := state.ledger
    taxLiability := state.taxLiability
    crmEventCount := state.crmEventCount
    logisticsEventCount := state.logisticsEventCount }

/-- Applying a stock-reserved event preserves stock and ledger validity. -/
theorem applyStockReservedEvent_preserves_validity
    (state : ValidSystemState)
    (sku : Sku) (quantity : Quantity)
    (hSku : state.stock.sku = sku)
    (hReserve : canReserve state.stock quantity) :
    let next := applyStockReservedEvent state sku quantity hSku hReserve
    next.stock.reserved ≤ next.stock.total ∧
      next.ledger.refunded ≤ next.ledger.captured := by
  simp [applyStockReservedEvent, reserveStock_preserves_safety]
  exact state.ledger.refunded_le_captured

/-- Apply a refund-issued event to the validated state when the amount is refundable. -/
def applyRefundIssuedEvent
    (state : ValidSystemState)
    (amount : Money)
    (hRefund : canRefund state.ledger amount) :
    ValidSystemState :=
  { stock := state.stock
    ledger := issueRefund state.ledger amount hRefund
    taxLiability := state.taxLiability
    crmEventCount := state.crmEventCount
    logisticsEventCount := state.logisticsEventCount }

/-- Applying a refund-issued event preserves stock and ledger validity. -/
theorem applyRefundIssuedEvent_preserves_validity
    (state : ValidSystemState)
    (amount : Money)
    (hRefund : canRefund state.ledger amount) :
    let next := applyRefundIssuedEvent state amount hRefund
    next.stock.reserved ≤ next.stock.total ∧
      next.ledger.refunded ≤ next.ledger.captured := by
  simp [applyRefundIssuedEvent, issueRefund_preserves_safety]
  exact state.stock.reserved_le_total

/-- Release reserved stock from the validated global state. -/
def applyReservationReleasedEvent
    (state : ValidSystemState)
    (sku : Sku) (quantity : Quantity)
    (_hSku : state.stock.sku = sku)
    (hReserved : quantity ≤ state.stock.reserved) :
    ValidSystemState :=
  { stock := releaseReservedStock state.stock quantity hReserved
    ledger := state.ledger
    taxLiability := state.taxLiability
    crmEventCount := state.crmEventCount
    logisticsEventCount := state.logisticsEventCount }

/-- Releasing reserved stock preserves stock and ledger validity. -/
theorem applyReservationReleasedEvent_preserves_validity
    (state : ValidSystemState)
    (sku : Sku) (quantity : Quantity)
    (hSku : state.stock.sku = sku)
    (hReserved : quantity ≤ state.stock.reserved) :
    let next := applyReservationReleasedEvent state sku quantity hSku hReserved
    next.stock.reserved ≤ next.stock.total ∧
      next.ledger.refunded ≤ next.ledger.captured := by
  simp [applyReservationReleasedEvent, releaseReservedStock_preserves_safety]
  exact state.ledger.refunded_le_captured

/-- Confirm shipment for stock that was already reserved. -/
def applyReservedShipmentConfirmedEvent
    (state : ValidSystemState)
    (sku : Sku) (quantity : Quantity)
    (_hSku : state.stock.sku = sku)
    (hReserved : quantity ≤ state.stock.reserved) :
    ValidSystemState :=
  { stock := confirmReservedShipment state.stock quantity hReserved
    ledger := state.ledger
    taxLiability := state.taxLiability
    crmEventCount := state.crmEventCount
    logisticsEventCount := state.logisticsEventCount }

/-- Confirming reserved shipment preserves stock and ledger validity. -/
theorem applyReservedShipmentConfirmedEvent_preserves_validity
    (state : ValidSystemState)
    (sku : Sku) (quantity : Quantity)
    (hSku : state.stock.sku = sku)
    (hReserved : quantity ≤ state.stock.reserved) :
    let next := applyReservedShipmentConfirmedEvent state sku quantity hSku hReserved
    next.stock.reserved ≤ next.stock.total ∧
      next.ledger.refunded ≤ next.ledger.captured := by
  simp [applyReservedShipmentConfirmedEvent,
    confirmReservedShipment_preserves_safety]
  exact state.ledger.refunded_le_captured

/-- Recording seller-side tax liability in the replay state. -/
def applyTaxLiabilityRecordedEvent
    (state : ValidSystemState) (amount : Money) : ValidSystemState :=
  { stock := state.stock
    ledger := state.ledger
    taxLiability := state.taxLiability + amount
    crmEventCount := state.crmEventCount
    logisticsEventCount := state.logisticsEventCount }

/-- Tax-liability projection preserves stock and ledger validity. -/
theorem applyTaxLiabilityRecordedEvent_preserves_validity
    (state : ValidSystemState) (amount : Money) :
    let next := applyTaxLiabilityRecordedEvent state amount
    next.stock.reserved ≤ next.stock.total ∧
      next.ledger.refunded ≤ next.ledger.captured := by
  simp [applyTaxLiabilityRecordedEvent]
  exact ⟨state.stock.reserved_le_total, state.ledger.refunded_le_captured⟩

/-- Tax-liability events add exactly the declared seller-side tax amount. -/
theorem applyTaxLiabilityRecordedEvent_taxLiability_eq
    (state : ValidSystemState) (amount : Money) :
    (applyTaxLiabilityRecordedEvent state amount).taxLiability =
      state.taxLiability + amount := by
  rfl

/-- Apply a CRM-domain event projection while preserving stock and payment safety. -/
def applyCRMProjectedEvent (state : ValidSystemState) : ValidSystemState :=
  { stock := state.stock
    ledger := state.ledger
    taxLiability := state.taxLiability
    crmEventCount := state.crmEventCount + 1
    logisticsEventCount := state.logisticsEventCount }

/-- CRM projected events preserve stock and ledger validity. -/
theorem applyCRMProjectedEvent_preserves_validity
    (state : ValidSystemState) :
    let next := applyCRMProjectedEvent state
    next.stock.reserved ≤ next.stock.total ∧
      next.ledger.refunded ≤ next.ledger.captured := by
  simp [applyCRMProjectedEvent]
  exact ⟨state.stock.reserved_le_total, state.ledger.refunded_le_captured⟩

/-- Applying a CRM projected event increments the CRM event counter. -/
theorem applyCRMProjectedEvent_increments_count (state : ValidSystemState) :
    (applyCRMProjectedEvent state).crmEventCount = state.crmEventCount + 1 := by
  rfl

/-- Apply a logistics-domain event projection while preserving stock and payment safety. -/
def applyLogisticsProjectedEvent (state : ValidSystemState) : ValidSystemState :=
  { stock := state.stock
    ledger := state.ledger
    taxLiability := state.taxLiability
    crmEventCount := state.crmEventCount
    logisticsEventCount := state.logisticsEventCount + 1 }

/-- Logistics projected events preserve stock and ledger validity. -/
theorem applyLogisticsProjectedEvent_preserves_validity
    (state : ValidSystemState) :
    let next := applyLogisticsProjectedEvent state
    next.stock.reserved ≤ next.stock.total ∧
      next.ledger.refunded ≤ next.ledger.captured := by
  simp [applyLogisticsProjectedEvent]
  exact ⟨state.stock.reserved_le_total, state.ledger.refunded_le_captured⟩

/-- Applying a logistics projected event increments the logistics event counter. -/
theorem applyLogisticsProjectedEvent_increments_count (state : ValidSystemState) :
    (applyLogisticsProjectedEvent state).logisticsEventCount =
      state.logisticsEventCount + 1 := by
  rfl

/--
A representative preservation theorem: reserving stock and issuing a valid
refund preserve the two key safety invariants of this simplified global state.
-/
theorem reserve_and_refund_preserve_validity
    (state : ValidSystemState)
    (reserveQty refundAmount : Nat)
    (hReserve : canReserve state.stock reserveQty)
    (hRefund : canRefund state.ledger refundAmount) :
    ∃ next : ValidSystemState,
      next.stock.reserved ≤ next.stock.total ∧ next.ledger.refunded ≤ next.ledger.captured := by
  let nextStock := reserveStock state.stock reserveQty hReserve
  let nextLedger := issueRefund state.ledger refundAmount hRefund
  refine ⟨{
    stock := nextStock
    ledger := nextLedger
    taxLiability := state.taxLiability
    crmEventCount := state.crmEventCount
    logisticsEventCount := state.logisticsEventCount }, ?_⟩
  constructor
  · exact nextStock.reserved_le_total
  · exact nextLedger.refunded_le_captured

/-! ### Semantic replay correctness -/

/-- Recording captured funds increases captured balance while preserving ledger safety. -/
def recordCapturedPayment (ledger : PaymentLedger) (amount : Money) : PaymentLedger :=
  { captured := ledger.captured + amount
    refunded := ledger.refunded
    refunded_le_captured :=
      ledger.refunded_le_captured.trans
        (Nat.le_add_right ledger.captured amount) }

/-- Captured-payment projection records exactly the additional captured amount. -/
theorem recordCapturedPayment_captured_eq
    (ledger : PaymentLedger) (amount : Money) :
    (recordCapturedPayment ledger amount).captured = ledger.captured + amount := by
  rfl

/-- Captured-payment projection leaves refunded balance unchanged. -/
theorem recordCapturedPayment_refunded_eq
    (ledger : PaymentLedger) (amount : Money) :
    (recordCapturedPayment ledger amount).refunded = ledger.refunded := by
  rfl

/--
Executable semantic projection for one domain event. The replay state now covers
stock, payment ledger, seller-side tax liability, CRM, and logistics counters;
order lifecycle events that do not affect those projections remain no-ops.
-/
def applyDomainEvent? (state : ValidSystemState) : DomainEvent → Option ValidSystemState
  | DomainEvent.OrderPlaced _ _ => some state
  | DomainEvent.PaymentCaptured _ amount =>
      some
        { stock := state.stock
          ledger := recordCapturedPayment state.ledger amount
          taxLiability := state.taxLiability
          crmEventCount := state.crmEventCount
          logisticsEventCount := state.logisticsEventCount }
  | DomainEvent.RefundIssued _ amount =>
      if hRefund : canRefund state.ledger amount then
        some (applyRefundIssuedEvent state amount hRefund)
      else
        none
  | DomainEvent.StockReserved sku quantity =>
      if hSku : state.stock.sku = sku then
        if hReserve : canReserve state.stock quantity then
          some (applyStockReservedEvent state sku quantity hSku hReserve)
        else
          none
      else
        none
  | DomainEvent.ReservationReleased sku quantity =>
      if hSku : state.stock.sku = sku then
        if hReserved : quantity ≤ state.stock.reserved then
          some (applyReservationReleasedEvent state sku quantity hSku hReserved)
        else
          none
      else
        none
  | DomainEvent.ReservedShipmentConfirmed sku quantity =>
      if hSku : state.stock.sku = sku then
        if hReserved : quantity ≤ state.stock.reserved then
          some
            (applyReservedShipmentConfirmedEvent
              state sku quantity hSku hReserved)
        else
          none
      else
        none
  | DomainEvent.TaxLiabilityRecorded _ amount =>
      some (applyTaxLiabilityRecordedEvent state amount)
  | DomainEvent.OrderShipped _ => some state
  | DomainEvent.LeadConverted _ _ => some (applyCRMProjectedEvent state)
  | DomainEvent.SupportCaseOpened _ _ => some (applyCRMProjectedEvent state)
  | DomainEvent.ShipmentPlanned _ _ => some (applyLogisticsProjectedEvent state)
  | DomainEvent.ShipmentDelivered _ => some (applyLogisticsProjectedEvent state)
  | DomainEvent.ReturnApproved _ _ _ => some (applyLogisticsProjectedEvent state)

/-- Executable replay for the semantic domain-event projection. -/
def replayDomainEvents? :
    ValidSystemState → List DomainEvent → Option ValidSystemState
  | state, [] => some state
  | state, event :: rest =>
      match applyDomainEvent? state event with
      | some next => replayDomainEvents? next rest
      | none => none

/-- One-event semantic projection is deterministic. -/
theorem applyDomainEvent?_deterministic
    {state before after : ValidSystemState} {event : DomainEvent}
    (hBefore : applyDomainEvent? state event = some before)
    (hAfter : applyDomainEvent? state event = some after) :
    before = after := by
  have hSome : (some before : Option ValidSystemState) = some after :=
    hBefore.symm.trans hAfter
  cases hSome
  rfl

/-- Semantic replay is deterministic for a fixed starting state and event list. -/
theorem replayDomainEvents?_deterministic
    {state before after : ValidSystemState} {events : List DomainEvent}
    (hBefore : replayDomainEvents? state events = some before)
    (hAfter : replayDomainEvents? state events = some after) :
    before = after := by
  have hSome : (some before : Option ValidSystemState) = some after :=
    hBefore.symm.trans hAfter
  cases hSome
  rfl

/-- Idempotent event application: already-processed keys do not re-apply events. -/
def applyIdempotentDomainEvent?
    (key : IdempotencyKey) (event : DomainEvent)
    (state : ValidSystemState) (idempotency : IdempotencyState) :
    Option (ValidSystemState × IdempotencyState) :=
  if alreadyProcessed key idempotency then
    some (state, idempotency)
  else
    match applyDomainEvent? state event with
    | some next => some (next, markProcessed key idempotency)
    | none => none

/-- A duplicate key leaves state and idempotency set unchanged. -/
theorem processed_idempotency_key_noops
    (key : IdempotencyKey) (event : DomainEvent)
    (state : ValidSystemState) (idempotency : IdempotencyState)
    (hProcessed : alreadyProcessed key idempotency) :
    applyIdempotentDomainEvent? key event state idempotency =
      some (state, idempotency) := by
  simp [applyIdempotentDomainEvent?, hProcessed]

/-- After a successful first application, replaying the same key is a no-op. -/
theorem duplicate_idempotency_key_does_not_apply_twice
    (key : IdempotencyKey) (event : DomainEvent)
    (state after : ValidSystemState) (idempotency : IdempotencyState)
    (hFresh : ¬ alreadyProcessed key idempotency)
    (hApply : applyDomainEvent? state event = some after) :
    applyIdempotentDomainEvent? key event state idempotency =
        some (after, markProcessed key idempotency) ∧
      applyIdempotentDomainEvent?
          key event after (markProcessed key idempotency) =
        some (after, markProcessed key idempotency) := by
  constructor
  · simp [applyIdempotentDomainEvent?, hFresh, hApply]
  · exact processed_idempotency_key_noops
      key event after (markProcessed key idempotency)
      (markProcessed_contains_key key idempotency)

/-- Stock reservation and refund projection commute because they touch disjoint state. -/
theorem stock_reservation_and_refund_commute
    (state : ValidSystemState) (sku : Sku) (quantity : Quantity)
    (refundAmount : Money)
    (hSku : state.stock.sku = sku)
    (hReserve : canReserve state.stock quantity)
    (hRefund : canRefund state.ledger refundAmount) :
    let afterReserve := applyStockReservedEvent state sku quantity hSku hReserve
    let afterRefund := applyRefundIssuedEvent state refundAmount hRefund
    applyRefundIssuedEvent afterReserve refundAmount hRefund =
      applyStockReservedEvent afterRefund sku quantity hSku hReserve := by
  rfl

/-- CRM and logistics projections commute because they increment independent counters. -/
theorem crm_and_logistics_projection_commute (state : ValidSystemState) :
    applyCRMProjectedEvent (applyLogisticsProjectedEvent state) =
      applyLogisticsProjectedEvent (applyCRMProjectedEvent state) := by
  rfl

/-- Snapshot used to resume semantic replay from a previously materialized state. -/
structure EventSnapshot where
  state : ValidSystemState
  lastSequence : Nat

/-- Resume semantic replay from a materialized snapshot. -/
def replayFromSnapshot? (snapshot : EventSnapshot) (events : List DomainEvent) :
    Option ValidSystemState :=
  replayDomainEvents? snapshot.state events

/-- Replaying an appended suffix from a replayed prefix is equivalent to full replay. -/
theorem replayDomainEvents?_append
    (state : ValidSystemState) (eventPrefix suffix : List DomainEvent) :
    replayDomainEvents? state (eventPrefix ++ suffix) =
      match replayDomainEvents? state eventPrefix with
      | some snapshot => replayDomainEvents? snapshot suffix
      | none => none := by
  induction eventPrefix generalizing state with
  | nil =>
      rfl
  | cons event rest ih =>
      cases hEvent : applyDomainEvent? state event with
      | none =>
          simp [replayDomainEvents?, hEvent]
      | some next =>
          simpa [replayDomainEvents?, hEvent] using ih next

/-- Replay from a snapshot is equivalent to replaying prefix then suffix. -/
theorem replay_from_snapshot_equivalent_to_full_replay
    (state snapshotState : ValidSystemState)
    (eventPrefix suffix : List DomainEvent) (lastSequence : Nat)
    (hPrefix : replayDomainEvents? state eventPrefix = some snapshotState) :
    replayDomainEvents? state (eventPrefix ++ suffix) =
      replayFromSnapshot?
        { state := snapshotState, lastSequence := lastSequence } suffix := by
  rw [replayDomainEvents?_append, hPrefix]
  rfl

/-! ### Ledger projection correctness -/

/-- Fold captured balance through payment-captured events. -/
def ledgerCapturedFold : Money → List DomainEvent → Money
  | captured, [] => captured
  | captured, DomainEvent.PaymentCaptured _ amount :: rest =>
      ledgerCapturedFold (captured + amount) rest
  | captured, _ :: rest => ledgerCapturedFold captured rest

/-- Fold refunded balance through refund-issued events. -/
def ledgerRefundedFold : Money → List DomainEvent → Money
  | refunded, [] => refunded
  | refunded, DomainEvent.RefundIssued _ amount :: rest =>
      ledgerRefundedFold (refunded + amount) rest
  | refunded, _ :: rest => ledgerRefundedFold refunded rest

/-- Fold seller-side tax liability through tax-liability events. -/
def taxLiabilityFold : Money → List DomainEvent → Money
  | liability, [] => liability
  | liability, DomainEvent.TaxLiabilityRecorded _ amount :: rest =>
      taxLiabilityFold (liability + amount) rest
  | liability, _ :: rest => taxLiabilityFold liability rest

/-- Project seller-side tax liability out of a domain event stream. -/
def projectTaxLiability (openingLiability : Money) (events : List DomainEvent) :
    Money :=
  taxLiabilityFold openingLiability events

/-- Tax-liability projection is exactly the fold over tax-liability events. -/
theorem projectTaxLiability_matches_fold
    (openingLiability : Money) (events : List DomainEvent) :
    projectTaxLiability openingLiability events =
      taxLiabilityFold openingLiability events := by
  rfl

/-- Project just the payment ledger out of a domain event stream. -/
def projectLedger? : PaymentLedger → List DomainEvent → Option PaymentLedger
  | ledger, [] => some ledger
  | ledger, DomainEvent.PaymentCaptured _ amount :: rest =>
      projectLedger? (recordCapturedPayment ledger amount) rest
  | ledger, DomainEvent.RefundIssued _ amount :: rest =>
      if hRefund : canRefund ledger amount then
        projectLedger? (issueRefund ledger amount hRefund) rest
      else
        none
  | ledger, _ :: rest => projectLedger? ledger rest

/--
If ledger projection succeeds, the resulting captured/refunded balances equal
the explicit folds of payment-captured and refund-issued events.
-/
theorem projectLedger?_matches_payment_refund_folds
    {ledger projected : PaymentLedger} {events : List DomainEvent}
    (h : projectLedger? ledger events = some projected) :
    projected.captured = ledgerCapturedFold ledger.captured events ∧
      projected.refunded = ledgerRefundedFold ledger.refunded events := by
  induction events generalizing ledger with
  | nil =>
      simp [projectLedger?] at h
      cases h
      simp [ledgerCapturedFold, ledgerRefundedFold]
  | cons event rest ih =>
      cases event with
      | OrderPlaced orderId amount =>
          have hFold := ih (ledger := ledger) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold] using hFold
      | PaymentCaptured orderId amount =>
          have hFold := ih (ledger := recordCapturedPayment ledger amount) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold, recordCapturedPayment]
            using hFold
      | RefundIssued orderId amount =>
          by_cases hRefund : canRefund ledger amount
          · have hFold := ih (ledger := issueRefund ledger amount hRefund) (by
              simpa [projectLedger?, hRefund] using h)
            simpa [ledgerCapturedFold, ledgerRefundedFold, issueRefund] using hFold
          · exfalso
            simp [projectLedger?, hRefund] at h
      | StockReserved sku quantity =>
          have hFold := ih (ledger := ledger) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold] using hFold
      | ReservationReleased sku quantity =>
          have hFold := ih (ledger := ledger) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold] using hFold
      | ReservedShipmentConfirmed sku quantity =>
          have hFold := ih (ledger := ledger) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold] using hFold
      | TaxLiabilityRecorded id amount =>
          have hFold := ih (ledger := ledger) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold] using hFold
      | OrderShipped orderId =>
          have hFold := ih (ledger := ledger) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold] using hFold
      | LeadConverted leadId opportunityId =>
          have hFold := ih (ledger := ledger) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold] using hFold
      | SupportCaseOpened caseId orderId =>
          have hFold := ih (ledger := ledger) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold] using hFold
      | ShipmentPlanned shipmentId orderId =>
          have hFold := ih (ledger := ledger) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold] using hFold
      | ShipmentDelivered shipmentId =>
          have hFold := ih (ledger := ledger) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold] using hFold
      | ReturnApproved authorizationId orderId amount =>
          have hFold := ih (ledger := ledger) (by
            simpa [projectLedger?] using h)
          simpa [ledgerCapturedFold, ledgerRefundedFold] using hFold

end CommerceTheory
