import CommerceTheory.EventSourcing

namespace CommerceTheory

/-! ## 16. Subscriptions, gift cards, chargebacks, returns, and cashflow -/

/-!
Post-purchase objects capture recurring subscriptions, gift-card redemption,
chargebacks, and cashflow plans. Each validated structure stores the bound that
makes downstream settlement calculations safe.
-/

/-- Closed set of recurring subscription lifecycle states. -/
inductive SubscriptionLifecycleStatus where
  | Active
  | Paused
  | PastDue
  | Cancelled
deriving DecidableEq, Repr

/-- Data shape for `SubscriptionPlan`; proof fields record invariants when needed. -/
structure SubscriptionPlan where
  price : Money
  periodDays : Days
  period_pos : 0 < periodDays

/-- Data shape for `RecurringSubscription`; proof fields record invariants when needed. -/
structure RecurringSubscription where
  customer : CustomerId
  plan : SubscriptionPlan
  status : SubscriptionLifecycleStatus
  currentBillingDate : Timestamp
  nextBillingDate : Timestamp
  next_after_current : currentBillingDate < nextBillingDate

/-- States the safety property captured by `subscription_next_after_current`. -/
theorem subscription_next_after_current (s : RecurringSubscription) :
    s.currentBillingDate < s.nextBillingDate := by
  exact s.next_after_current

/-- Data shape for `GiftCard`; proof fields record invariants when needed. -/
structure GiftCard where
  balance : Money
  expiresAt : Timestamp

/-- Data shape for `GiftCardRedemption`; proof fields record invariants when needed. -/
structure GiftCardRedemption where
  card : GiftCard
  amount : Money
  amount_le_balance : amount ≤ card.balance

/-- Computes or checks `giftCardBalanceAfterRedeem` using the validated data in this module. -/
def giftCardBalanceAfterRedeem (r : GiftCardRedemption) : Money :=
  r.card.balance - r.amount

/-- States the safety property captured by `giftCardBalanceAfterRedeem_le_balance`. -/
theorem giftCardBalanceAfterRedeem_le_balance (r : GiftCardRedemption) :
    giftCardBalanceAfterRedeem r ≤ r.card.balance := by
  unfold giftCardBalanceAfterRedeem
  exact Nat.sub_le r.card.balance r.amount

/-- Redeemed amount plus remaining gift-card balance recovers the original balance. -/
theorem giftCardBalanceAfterRedeem_add_amount_eq_balance (r : GiftCardRedemption) :
    giftCardBalanceAfterRedeem r + r.amount = r.card.balance := by
  unfold giftCardBalanceAfterRedeem
  exact Nat.sub_add_cancel r.amount_le_balance

/-- A gift card is usable at a timestamp only before or at expiry. -/
def giftCardValidAt (now : Timestamp) (card : GiftCard) : Prop :=
  now ≤ card.expiresAt

/-- A redemption with a valid timestamp exposes its expiry check. -/
theorem giftCardRedemption_not_expired
    (now : Timestamp) (r : GiftCardRedemption)
    (h : giftCardValidAt now r.card) :
    now ≤ r.card.expiresAt := by
  exact h

/-- Data shape for `Chargeback`; proof fields record invariants when needed. -/
structure Chargeback where
  paymentAmount : Money
  chargebackAmount : Money
  amount_le_payment : chargebackAmount ≤ paymentAmount

/-- States the safety property captured by `chargeback_amount_safe`. -/
theorem chargeback_amount_safe (c : Chargeback) :
    c.chargebackAmount ≤ c.paymentAmount := by
  exact c.amount_le_payment

/-- Data shape for `CashflowEvent`; proof fields record invariants when needed. -/
structure CashflowEvent where
  inflow : Money
  outflow : Money

/-- Sum cash inflows across projected cashflow events. -/
def cashflowInflowsTotal : List CashflowEvent → Money
  | [] => 0
  | e :: rest => e.inflow + cashflowInflowsTotal rest

/-- Sum cash outflows across projected cashflow events. -/
def cashflowOutflowsTotal : List CashflowEvent → Money
  | [] => 0
  | e :: rest => e.outflow + cashflowOutflowsTotal rest

/-- Data shape for `CashflowPlan`; proof fields record invariants when needed. -/
structure CashflowPlan where
  startingCash : Money
  requiredReserve : Money
  expectedInflows : Money
  expectedOutflows : Money
  reserve_safe : requiredReserve + expectedOutflows ≤ startingCash + expectedInflows

/-- States the safety property captured by `cashflowPlan_safe`. -/
theorem cashflowPlan_safe (p : CashflowPlan) :
    p.requiredReserve + p.expectedOutflows ≤ p.startingCash + p.expectedInflows := by
  exact p.reserve_safe

/-- A cashflow plan can be justified by event totals without losing safety. -/
theorem cashflowPlan_safe_from_events
    (p : CashflowPlan) (events : List CashflowEvent)
    (hin : cashflowInflowsTotal events = p.expectedInflows)
    (hout : cashflowOutflowsTotal events = p.expectedOutflows) :
    p.requiredReserve + cashflowOutflowsTotal events ≤
      p.startingCash + cashflowInflowsTotal events := by
  rw [hout, hin]
  exact p.reserve_safe

/-- Event-backed cashflow plan with its reserve safety stated over event totals. -/
structure EventBackedCashflowPlan where
  startingCash : Money
  requiredReserve : Money
  events : List CashflowEvent
  reserve_safe :
    requiredReserve + cashflowOutflowsTotal events ≤
      startingCash + cashflowInflowsTotal events

/-- Event-backed cashflow plans preserve the reserve-safety invariant. -/
theorem eventBackedCashflowPlan_safe (p : EventBackedCashflowPlan) :
    p.requiredReserve + cashflowOutflowsTotal p.events ≤
      p.startingCash + cashflowInflowsTotal p.events := by
  exact p.reserve_safe


end CommerceTheory
