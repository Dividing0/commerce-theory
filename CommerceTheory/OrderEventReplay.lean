import CommerceTheory.EventSourcing

namespace CommerceTheory

/-! # Order-aware replay

The aggregate projection is useful for reporting, but cannot enforce refund
bounds for individual orders. This projection registers orders explicitly and
keeps a separate proof-carrying payment ledger for each order. Missing orders
have no payment authority. The order table is a function so updates have a
simple executable lookup semantics and a precise noninterference theorem.
-/

/-- Payment ledgers indexed by order identity; `none` means unregistered. -/
abbrev OrderPaymentState := OrderId → Option PaymentLedger

/-- No orders have been registered in a fresh payment projection. -/
def emptyOrderPaymentState : OrderPaymentState := fun _ => none

/-- Replace one order's ledger, preserving every other order's balance. -/
def setOrderPaymentLedger (payments : OrderPaymentState)
    (orderId : OrderId) (ledger : PaymentLedger) : OrderPaymentState :=
  fun queried => if queried = orderId then some ledger else payments queried

@[simp] theorem setOrderPaymentLedger_same (payments : OrderPaymentState)
    (orderId : OrderId) (ledger : PaymentLedger) :
    setOrderPaymentLedger payments orderId ledger orderId = some ledger := by
  simp [setOrderPaymentLedger]

@[simp] theorem setOrderPaymentLedger_other (payments : OrderPaymentState)
    (orderId other : OrderId) (ledger : PaymentLedger) (h : other ≠ orderId) :
    setOrderPaymentLedger payments orderId ledger other = payments other := by
  simp [setOrderPaymentLedger, h]

/-- Register a new order, capture its funds, or refund only its own captured balance.
Duplicate placement and payment events for unregistered orders are rejected.
Events outside the payment projection leave the table unchanged. -/
def applyOrderPaymentEvent? (payments : OrderPaymentState) :
    DomainEvent → Option OrderPaymentState
  | .OrderPlaced orderId _ =>
      match payments orderId with
      | some _ => none
      | none => some (setOrderPaymentLedger payments orderId
          { captured := 0, refunded := 0, refunded_le_captured := Nat.le_refl 0 })
  | .PaymentCaptured orderId amount =>
      match payments orderId with
      | none => none
      | some ledger =>
          some (setOrderPaymentLedger payments orderId (recordCapturedPayment ledger amount))
  | .RefundIssued orderId amount =>
      match payments orderId with
      | none => none
      | some ledger =>
          if hRefund : canRefund ledger amount then
            some (setOrderPaymentLedger payments orderId (issueRefund ledger amount hRefund))
          else none
  | _ => some payments

/-- A capture cannot silently create an order. -/
theorem applyOrderPaymentEvent?_unknown_capture (payments : OrderPaymentState)
    (orderId : OrderId) (amount : Money) (h : payments orderId = none) :
    applyOrderPaymentEvent? payments (.PaymentCaptured orderId amount) = none := by
  simp [applyOrderPaymentEvent?, h]

/-- A refund cannot use an unregistered order identity. -/
theorem applyOrderPaymentEvent?_unknown_refund (payments : OrderPaymentState)
    (orderId : OrderId) (amount : Money) (h : payments orderId = none) :
    applyOrderPaymentEvent? payments (.RefundIssued orderId amount) = none := by
  simp [applyOrderPaymentEvent?, h]

/-- An order's remaining balance is the only source of refund authority. -/
theorem applyOrderPaymentEvent?_excess_refund (payments : OrderPaymentState)
    (orderId : OrderId) (ledger : PaymentLedger) (amount : Money)
    (hLedger : payments orderId = some ledger) (hRefund : ¬ canRefund ledger amount) :
    applyOrderPaymentEvent? payments (.RefundIssued orderId amount) = none := by
  simp [applyOrderPaymentEvent?, hLedger, hRefund]

/-- Duplicate placement cannot reset an existing order's ledger. -/
theorem applyOrderPaymentEvent?_duplicate_order (payments : OrderPaymentState)
    (orderId : OrderId) (ledger : PaymentLedger) (total : Money)
    (h : payments orderId = some ledger) :
    applyOrderPaymentEvent? payments (.OrderPlaced orderId total) = none := by
  simp [applyOrderPaymentEvent?, h]

/-- Successful capture records exactly the additional funds for the supplied order. -/
theorem applyOrderPaymentEvent?_capture (payments : OrderPaymentState)
    (orderId : OrderId) (ledger : PaymentLedger) (amount : Money)
    (h : payments orderId = some ledger) :
    applyOrderPaymentEvent? payments (.PaymentCaptured orderId amount) =
      some (setOrderPaymentLedger payments orderId (recordCapturedPayment ledger amount)) := by
  simp [applyOrderPaymentEvent?, h]

/-- Successful refund records the amount in the supplied order's ledger. -/
theorem applyOrderPaymentEvent?_refund (payments : OrderPaymentState)
    (orderId : OrderId) (ledger : PaymentLedger) (amount : Money)
    (h : payments orderId = some ledger) (hRefund : canRefund ledger amount) :
    applyOrderPaymentEvent? payments (.RefundIssued orderId amount) =
      some (setOrderPaymentLedger payments orderId (issueRefund ledger amount hRefund)) := by
  simp [applyOrderPaymentEvent?, h, hRefund]

/-- Acceptance of a refund implies authority from the original order ledger,
and the returned table contains exactly that order's updated ledger. -/
theorem applyOrderPaymentEvent?_refund_authorized
    {payments after : OrderPaymentState} (orderId : OrderId) (amount : Money)
    (hApply : applyOrderPaymentEvent? payments (.RefundIssued orderId amount) = some after) :
    ∃ ledger : PaymentLedger, payments orderId = some ledger ∧
      ∃ hRefund : canRefund ledger amount,
        after orderId = some (issueRefund ledger amount hRefund) := by
  simp only [applyOrderPaymentEvent?] at hApply
  split at hApply
  · cases hApply
  · rename_i ledger hLedger
    split at hApply
    · rename_i hRefund
      cases hApply
      exact ⟨ledger, hLedger, hRefund, setOrderPaymentLedger_same _ _ _⟩
    · cases hApply

/-- A payment event's order identity, or `none` for unrelated projections. -/
def paymentEventOrderId : DomainEvent → Option OrderId
  | .OrderPlaced orderId _ => some orderId
  | .PaymentCaptured orderId _ => some orderId
  | .RefundIssued orderId _ => some orderId
  | _ => none

/-- Accepted payment events leave every other order's ledger unchanged. -/
theorem applyOrderPaymentEvent?_other_order
    {payments after : OrderPaymentState} {event : DomainEvent} (other : OrderId)
    (hOther : paymentEventOrderId event ≠ some other)
    (hApply : applyOrderPaymentEvent? payments event = some after) :
    after other = payments other := by
  -- Every accepted branch either returns `payments` or updates the event's own order.
  cases event <;> simp only [applyOrderPaymentEvent?] at hApply <;>
    simp only [paymentEventOrderId, ne_eq, Option.some.injEq] at hOther <;>
    repeat' (first | split at hApply | (cases hApply))
  all_goals first
    | rfl
    | exact setOrderPaymentLedger_other _ _ _ _ (Ne.symm hOther)

/-- Aggregate reporting state together with payment authority for each order. -/
structure OrderAwareSystemState where
  system : ValidSystemState
  payments : OrderPaymentState

/-- Start an order-aware replay with empty, consistent payment projections. -/
def initialOrderAwareSystemState (stock : StockState) : OrderAwareSystemState :=
  { system :=
      { stock := stock
        ledger := { captured := 0, refunded := 0, refunded_le_captured := Nat.le_refl 0 }
        taxLiability := 0
        crmEventCount := 0
        logisticsEventCount := 0 }
    payments := emptyOrderPaymentState }

/-- Apply the order check and aggregate projection as one atomic operation. -/
def applyOrderAwareDomainEvent? (state : OrderAwareSystemState) (event : DomainEvent) :
    Option OrderAwareSystemState := do
  let payments ← applyOrderPaymentEvent? state.payments event
  let system ← applyDomainEvent? state.system event
  some { system := system, payments := payments }

/-- Replay payloads with per-order payment checks; envelope replay also checks sequences. -/
def replayOrderAwareDomainEvents? :
    OrderAwareSystemState → List DomainEvent → Option OrderAwareSystemState
  | state, [] => some state
  | state, event :: rest =>
      match applyOrderAwareDomainEvent? state event with
      | some next => replayOrderAwareDomainEvents? next rest
      | none => none

/-- A failed order payment check rejects the complete system update. -/
theorem applyOrderAwareDomainEvent?_payment_rejected
    (state : OrderAwareSystemState) (event : DomainEvent)
    (h : applyOrderPaymentEvent? state.payments event = none) :
    applyOrderAwareDomainEvent? state event = none := by
  simp [applyOrderAwareDomainEvent?, h]

/-- Successful system application uses precisely the accepted payment-table update. -/
theorem applyOrderAwareDomainEvent?_payments
    {state after : OrderAwareSystemState} {event : DomainEvent}
    (h : applyOrderAwareDomainEvent? state event = some after) :
    applyOrderPaymentEvent? state.payments event = some after.payments := by
  simp only [applyOrderAwareDomainEvent?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨payments, hPayments, system, -, rfl⟩ := h
  exact hPayments

/-- An unrelated order is unchanged by the complete system update. -/
theorem applyOrderAwareDomainEvent?_other_order
    {state after : OrderAwareSystemState} {event : DomainEvent} (other : OrderId)
    (hOther : paymentEventOrderId event ≠ some other)
    (hApply : applyOrderAwareDomainEvent? state event = some after) :
    after.payments other = state.payments other :=
  applyOrderPaymentEvent?_other_order other hOther
    (applyOrderAwareDomainEvent?_payments hApply)

/-- Replaying any list of events for other orders preserves this order's balance. -/
theorem replayOrderAwareDomainEvents?_other_order
    {state after : OrderAwareSystemState} {events : List DomainEvent} (other : OrderId)
    (hOther : ∀ event ∈ events, paymentEventOrderId event ≠ some other)
    (hReplay : replayOrderAwareDomainEvents? state events = some after) :
    after.payments other = state.payments other := by
  induction events generalizing state with
  | nil => cases hReplay; rfl
  | cons event rest ih =>
      simp only [replayOrderAwareDomainEvents?] at hReplay
      split at hReplay
      · rename_i next hApply
        exact (ih (fun e he => hOther e (List.mem_cons_of_mem event he)) hReplay).trans
          (applyOrderAwareDomainEvent?_other_order other (hOther event List.mem_cons_self) hApply)
      · cases hReplay

/-- Order-aware replay snapshots retain both projections and the accepted cursor. -/
abbrev OrderAwareEventSnapshot := ReplaySnapshot OrderAwareSystemState

/-- Resume order-aware replay, rejecting stale, duplicate, and unordered envelopes. -/
def replayOrderAwareFromSnapshot? (snapshot : OrderAwareEventSnapshot)
    (events : List EventEnvelope) : Option OrderAwareEventSnapshot :=
  replaySequencedEvents? applyOrderAwareDomainEvent? snapshot events

/-- Ordered envelope replay computes exactly the order-aware payload projection. -/
theorem replayOrderAwareFromSnapshot?_state_of_ordered
    (snapshot : OrderAwareEventSnapshot) (events : List EventEnvelope)
    (hOrdered : streamSequencesStrictlyIncreaseFrom snapshot.lastSequence events) :
    (replayOrderAwareFromSnapshot? snapshot events).map (fun next => next.state) =
      replayOrderAwareDomainEvents? snapshot.state (events.map (fun envelope => envelope.event)) := by
  induction events generalizing snapshot with
  | nil => rfl
  | cons envelope rest ih =>
      cases hApply : applyOrderAwareDomainEvent? snapshot.state envelope.event with
      | none =>
          simp [replayOrderAwareFromSnapshot?, replaySequencedEvents?,
            replayOrderAwareDomainEvents?, hOrdered.left, hApply]
      | some next =>
          simpa [replayOrderAwareFromSnapshot?, replaySequencedEvents?,
            replayOrderAwareDomainEvents?, hOrdered.left, hApply] using
            ih { state := next, lastSequence := envelope.sequence } hOrdered.right

/-- Snapshot resumption cannot change an order absent from the payment events. -/
theorem replayOrderAwareFromSnapshot?_other_order
    {snapshot after : OrderAwareEventSnapshot} {events : List EventEnvelope} (other : OrderId)
    (hOther : ∀ envelope ∈ events, paymentEventOrderId envelope.event ≠ some other)
    (hReplay : replayOrderAwareFromSnapshot? snapshot events = some after) :
    after.state.payments other = snapshot.state.payments other := by
  have hOrdered := replaySequencedEvents?_ordered applyOrderAwareDomainEvent? hReplay
  have hPayload : replayOrderAwareDomainEvents? snapshot.state
      (events.map (fun envelope => envelope.event)) = some after.state := by
    rw [← replayOrderAwareFromSnapshot?_state_of_ordered snapshot events hOrdered, hReplay]
    rfl
  apply replayOrderAwareDomainEvents?_other_order other _ hPayload
  intro event hEvent
  obtain ⟨envelope, hMem, rfl⟩ := List.mem_map.mp hEvent
  exact hOther envelope hMem

/-- Resuming a replayed prefix has exactly the same result as replaying both parts. -/
theorem replayOrderAwareFromSnapshot?_append
    (snapshot next : OrderAwareEventSnapshot) (eventPrefix suffix : List EventEnvelope)
    (hPrefix : replayOrderAwareFromSnapshot? snapshot eventPrefix = some next) :
    replayOrderAwareFromSnapshot? snapshot (eventPrefix ++ suffix) =
      replayOrderAwareFromSnapshot? next suffix := by
  unfold replayOrderAwareFromSnapshot? at *
  rw [replaySequencedEvents?_append, hPrefix]

end CommerceTheory
