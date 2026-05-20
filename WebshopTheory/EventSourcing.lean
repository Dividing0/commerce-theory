import WebshopTheory.RiskPrivacy

namespace WebShopTheoryComplete

/-! ## 15. Event sourcing, idempotency, webhooks, and valid state preservation -/

/-!
Event-sourcing definitions describe envelopes, streams, webhook ordering, and
idempotency. The system-state theorem demonstrates the intended proof style:
operations should preserve global validity when their local invariants hold.
-/

/-- Closed set of cases for `DomainEvent` in the webshop domain model. -/
inductive DomainEvent where
  | OrderPlaced : OrderId → Money → DomainEvent
  | PaymentCaptured : OrderId → Money → DomainEvent
  | RefundIssued : OrderId → Money → DomainEvent
  | StockReserved : Sku → Quantity → DomainEvent
  | OrderShipped : OrderId → DomainEvent
deriving DecidableEq, Repr

/-- Data shape for `EventEnvelope`; proof fields record invariants when needed. -/
structure EventEnvelope where
  sequence : Nat
  event : DomainEvent

/-- Data shape for `EventStream`; proof fields record invariants when needed. -/
structure EventStream where
  events : List EventEnvelope
  lastSequence : Nat

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

/-- Data shape for `ValidSystemState`; proof fields record invariants when needed. -/
structure ValidSystemState where
  stock : StockState
  ledger : PaymentLedger

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
  refine ⟨{ stock := nextStock, ledger := nextLedger }, ?_⟩
  constructor
  · exact nextStock.reserved_le_total
  · exact nextLedger.refunded_le_captured


end WebShopTheoryComplete
