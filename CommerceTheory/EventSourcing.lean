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

/-- Apply a CRM-domain event projection while preserving stock and payment safety. -/
def applyCRMProjectedEvent (state : ValidSystemState) : ValidSystemState :=
  { stock := state.stock
    ledger := state.ledger
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
    crmEventCount := state.crmEventCount
    logisticsEventCount := state.logisticsEventCount }, ?_⟩
  constructor
  · exact nextStock.reserved_le_total
  · exact nextLedger.refunded_le_captured


end CommerceTheory
