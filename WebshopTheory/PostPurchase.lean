import WebshopTheory.EventSourcing

namespace WebShopTheoryComplete

/-! ## 16. Subscriptions, gift cards, chargebacks, returns, and cashflow -/

/-!
Post-purchase objects capture recurring subscriptions, gift-card redemption,
chargebacks, and cashflow plans. Each validated structure stores the bound that
makes downstream settlement calculations safe.
-/

/-- Closed set of cases for `SubscriptionStatus2` in the webshop domain model. -/
inductive SubscriptionStatus2 where
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
  status : SubscriptionStatus2
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


end WebShopTheoryComplete
