import Mathlib
import Timelib

namespace CommerceTheory

/-! ## 0. Foundations -/

/-!
This module defines the shared vocabulary used by the rest of the theory.

Commercial amounts use explicit domain names instead of broad `Nat` aliases:
non-negative money is fixed-scale minor units, signed profit/loss is an integer,
and decimal money can carry an explicit scale when a proof needs to discuss a
pre-rounded value. Date/time values are backed by `ammkrn/timelib` so timestamps
and elapsed durations are no longer plain natural numbers. Operational counts,
weights, and ids remain non-negative by construction, but each now has a named
commercial role.
-/

/-- Minor units are fixed-scale units such as cents, kopiykas, or pence. -/
abbrev MinorUnit := Nat
/-- Non-negative money in fixed-scale minor units. -/
abbrev NonNegMoney := MinorUnit
/-- Signed money, used for profit/loss and other calculations that can go below zero. -/
abbrev SignedMoney := Int

/--
Decimal money carries a signed coefficient plus a decimal scale. For example,
`coefficient = 12345, scale = 2` represents 123.45 in the relevant currency.
-/
structure DecimalMoney where
  coefficient : Int
  scale : Nat
deriving DecidableEq, Repr

/-- Public money type used throughout existing commerce invariants. -/
abbrev Money := NonNegMoney
/-- Non-negative item or unit counts. -/
abbrev Quantity := Nat
/-- Non-negative shipment/package weight units chosen by the model. -/
abbrev Weight := Nat
/-- Proleptic Gregorian date from `timelib`. -/
abbrev Date := Timelib.Ymd
/-- Proleptic Gregorian naive timestamp at second precision from `timelib`. -/
abbrev Timestamp := Timelib.NaiveDateTime 0
/-- Elapsed duration at second precision from `timelib`. -/
abbrev Duration := Timelib.SignedDuration 0
/-- Business day windows represented as exact second-precision durations. -/
abbrev Days := Duration
/-- Non-negative opaque runtime id values. -/
abbrev Id := Nat

/-! ### Date/time helpers -/

/-- Construct a second-precision timestamp from Gregorian date and wall-clock fields. -/
def timestampFromYmdhms?
    (year : Int) (month day hour minute second : Nat) : Option Timestamp :=
  Timelib.NaiveDateTime.fromYmdhms?
    (siPow := 0) year month day hour minute second

/-- The Unix epoch as a `Timestamp`. -/
def unixEpochTimestamp : Timestamp :=
  Timelib.NaiveDateTime.unixEpoch (siPow := 0) (by decide)

/-- Compute elapsed time between two timestamps. -/
def timestampAge (now observedAt : Timestamp) : Duration :=
  now - observedAt

/-- Convert a natural number of whole days into the model's elapsed-duration type. -/
def days (n : Nat) : Days :=
  Timelib.SignedDuration.oneDay (siPow := 0) (by decide) * Int.ofNat n

/-! ### Rounding and signed money helpers -/

/-- Supported rounding policies for converting rational commercial amounts to minor units. -/
inductive RoundingMode where
  | Floor
  | Ceiling
  | HalfUp
deriving DecidableEq, Repr

/--
Round a natural numerator divided by a natural denominator to fixed-scale minor
units according to an explicit mode. Validated finance structures carry a proof
that they used their declared mode.
-/
def roundDiv (mode : RoundingMode) (numerator denominator : Nat) : Nat :=
  match mode with
  | RoundingMode.Floor => numerator / denominator
  | RoundingMode.Ceiling =>
      if numerator % denominator = 0 then numerator / denominator else numerator / denominator + 1
  | RoundingMode.HalfUp => (numerator + denominator / 2) / denominator

/-- Round an exact rational money numerator into non-negative minor units. -/
def roundMoney (mode : RoundingMode) (numerator denominator : Nat) : Money :=
  roundDiv mode numerator denominator

/-- Floor-rounding residual, measured in denominator-scaled minor units. -/
def floorRoundingRemainder (numerator denominator : Nat) : Nat :=
  numerator % denominator

/-- Floor rounding decomposes an exact numerator into rounded units plus residual. -/
theorem floorRoundDiv_decomposition (numerator denominator : Nat) :
    roundDiv RoundingMode.Floor numerator denominator * denominator +
      floorRoundingRemainder numerator denominator = numerator := by
  unfold roundDiv floorRoundingRemainder
  exact Nat.div_add_mod' numerator denominator

/-- A single floor-rounded amount loses less than one minor unit. -/
theorem floorRoundingRemainder_lt_denominator
    (numerator denominator : Nat) (hden : 0 < denominator) :
    floorRoundingRemainder numerator denominator < denominator := by
  unfold floorRoundingRemainder
  exact Nat.mod_lt numerator hden

/-- A single floor-rounded amount loses at most one minor unit. -/
theorem floorRoundingRemainder_le_denominator
    (numerator denominator : Nat) (hden : 0 < denominator) :
    floorRoundingRemainder numerator denominator ≤ denominator := by
  exact (floorRoundingRemainder_lt_denominator numerator denominator hden).le

/-- Sum of floor-rounding residuals for a group of rounded lines/items. -/
def floorRoundedLinesRemainderTotal (denominator : Nat) : List Nat → Nat
  | [] => 0
  | numerator :: rest =>
      floorRoundingRemainder numerator denominator +
        floorRoundedLinesRemainderTotal denominator rest

/--
Per-line floor rounding error is bounded by one minor unit per rounded line.
The error is expressed in denominator-scaled minor units, so `denominator`
corresponds to one output minor unit.
-/
theorem floorRoundedLinesRemainderTotal_le_one_minor_unit_per_line
    (denominator : Nat) (numerators : List Nat) (hden : 0 < denominator) :
    floorRoundedLinesRemainderTotal denominator numerators ≤
      numerators.length * denominator := by
  induction numerators with
  | nil =>
      simp [floorRoundedLinesRemainderTotal]
  | cons numerator rest ih =>
      have hline :
          floorRoundingRemainder numerator denominator ≤ denominator :=
        floorRoundingRemainder_le_denominator numerator denominator hden
      calc
        floorRoundedLinesRemainderTotal denominator (numerator :: rest)
            = floorRoundingRemainder numerator denominator +
                floorRoundedLinesRemainderTotal denominator rest := by
              rfl
        _ ≤ denominator + rest.length * denominator := by
              exact Nat.add_le_add hline ih
        _ = (numerator :: rest).length * denominator := by
              simp [Nat.succ_mul, Nat.add_comm]

/-- A wrapper type for SKUs, so a SKU cannot be accidentally used as another id. -/
structure Sku where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `ProductId`; proof fields record invariants when needed. -/
structure ProductId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `VariantId`; proof fields record invariants when needed. -/
structure VariantId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `CustomerId`; proof fields record invariants when needed. -/
structure CustomerId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `OrderId`; proof fields record invariants when needed. -/
structure OrderId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `PaymentId`; proof fields record invariants when needed. -/
structure PaymentId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `SupplierId`; proof fields record invariants when needed. -/
structure SupplierId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `MarketplaceOrderId`; proof fields record invariants when needed. -/
structure MarketplaceOrderId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `CampaignId`; proof fields record invariants when needed. -/
structure CampaignId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `CompetitorId`; proof fields record invariants when needed. -/
structure CompetitorId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `IdempotencyKey`; proof fields record invariants when needed. -/
structure IdempotencyKey where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `AccountId`; proof fields record invariants when needed. -/
structure AccountId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `ContactId`; proof fields record invariants when needed. -/
structure ContactId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `LeadId`; proof fields record invariants when needed. -/
structure LeadId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `OpportunityId`; proof fields record invariants when needed. -/
structure OpportunityId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `InteractionId`; proof fields record invariants when needed. -/
structure InteractionId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `SegmentId`; proof fields record invariants when needed. -/
structure SegmentId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `SupportCaseId`; proof fields record invariants when needed. -/
structure SupportCaseId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `ShipmentId`; proof fields record invariants when needed. -/
structure ShipmentId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `TrackingEventId`; proof fields record invariants when needed. -/
structure TrackingEventId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `TransferId`; proof fields record invariants when needed. -/
structure TransferId where
  value : Nat
deriving DecidableEq, Repr

/-- Data shape for `ReturnAuthorizationId`; proof fields record invariants when needed. -/
structure ReturnAuthorizationId where
  value : Nat
deriving DecidableEq, Repr

/-- Closed set of cases for `Currency` in the commerce domain model. -/
inductive Currency where
  | UAH
  | USD
  | EUR
  | GBP
  | PLN
deriving DecidableEq, Repr

/--
Money tagged with a currency at the type level.

For example, `MoneyIn Currency.USD` and `MoneyIn Currency.EUR` are different
types, so Lean will not let code add them without an explicit conversion.
-/
structure MoneyIn (c : Currency) where
  amount : Money

namespace MoneyIn

/-- The zero amount in a specific currency. -/
protected def zero (c : Currency) : MoneyIn c :=
  { amount := 0 }

/-- Add two amounts only when Lean knows they have the same currency type. -/
protected def add {c : Currency} (a b : MoneyIn c) : MoneyIn c :=
  { amount := a.amount + b.amount }

/--
Natural-number subtraction floors at zero in Lean.
This is useful for conservative business calculations such as remaining balance.
-/
protected def sub {c : Currency} (a b : MoneyIn c) : MoneyIn c :=
  { amount := a.amount - b.amount }

/-- States the safety property captured by `add_amount`. -/
theorem add_amount {c : Currency} (a b : MoneyIn c) :
    (MoneyIn.add a b).amount = a.amount + b.amount := by
  rfl

/-- The zero amount has value zero in its currency. -/
theorem zero_amount (c : Currency) :
    (MoneyIn.zero c).amount = 0 := by
  rfl

/-- Adding zero on the right preserves the amount. -/
theorem add_zero_amount {c : Currency} (a : MoneyIn c) :
    (MoneyIn.add a (MoneyIn.zero c)).amount = a.amount := by
  simp [MoneyIn.add, MoneyIn.zero]

/-- Adding zero on the left preserves the amount. -/
theorem zero_add_amount {c : Currency} (a : MoneyIn c) :
    (MoneyIn.add (MoneyIn.zero c) a).amount = a.amount := by
  simp [MoneyIn.add, MoneyIn.zero]

/-- Currency-safe money addition is commutative at the amount level. -/
theorem add_amount_comm {c : Currency} (a b : MoneyIn c) :
    (MoneyIn.add a b).amount = (MoneyIn.add b a).amount := by
  simp [MoneyIn.add, Nat.add_comm]

/-- States the safety property captured by `sub_le_left`. -/
theorem sub_le_left {c : Currency} (a b : MoneyIn c) :
    (MoneyIn.sub a b).amount ≤ a.amount := by
  unfold MoneyIn.sub
  exact Nat.sub_le a.amount b.amount

end MoneyIn

/-- Data shape for `MoneyAmount`; proof fields record invariants when needed. -/
structure MoneyAmount where
  amount : Money
  currency : Currency

/-- Runtime-style currency equality for values whose currency is stored as data. -/
def sameCurrency (a b : MoneyAmount) : Prop :=
  a.currency = b.currency

/-- States the safety property captured by `sameCurrency_symmetric`. -/
theorem sameCurrency_symmetric (a b : MoneyAmount) (h : sameCurrency a b) :
    sameCurrency b a := by
  unfold sameCurrency at *
  exact h.symm

/-- Runtime-style currency equality is reflexive. -/
theorem sameCurrency_refl (a : MoneyAmount) :
    sameCurrency a a := by
  rfl

/-- Runtime-style currency equality is transitive. -/
theorem sameCurrency_trans
    (a b c : MoneyAmount) (hab : sameCurrency a b) (hbc : sameCurrency b c) :
    sameCurrency a c := by
  unfold sameCurrency at *
  exact hab.trans hbc

/--
Basis points are hundredths of a percent. The proof field prevents values above
10000, so this can represent rates from 0% through 100%.
-/
structure BasisPoints where
  value : Nat
  value_le_10000 : value ≤ 10000

/-- Apply a basis-point rate to a non-negative amount using integer division. -/
def applyBps (bp : BasisPoints) (amount : Money) : Money :=
  amount * bp.value / 10000

/-- Apply a basis-point rate with an explicit rounding mode. -/
def roundBpsAmount (mode : RoundingMode) (amount : Money) (bp : BasisPoints) : Money :=
  roundMoney mode (amount * bp.value) 10000

/-- States the safety property captured by `bps_mul_bound`. -/
theorem bps_mul_bound (bp : BasisPoints) (amount : Money) :
    amount * bp.value ≤ amount * 10000 := by
  exact Nat.mul_le_mul_left amount bp.value_le_10000

/-- Applying a basis-point rate between 0% and 100% never exceeds the amount. -/
theorem applyBps_le_amount (bp : BasisPoints) (amount : Money) :
    applyBps bp amount ≤ amount := by
  unfold applyBps
  exact Nat.div_le_of_le_mul (by
    simpa [Nat.mul_comm] using bps_mul_bound bp amount)

/-- Conservative non-negative profit floors at zero for legacy margin guarantees. -/
def profitAmount (revenue totalCosts : Money) : Money :=
  revenue - totalCosts

/-- Signed profit/loss preserves losses instead of flooring negative results to zero. -/
def profitLossAmount (revenue totalCosts : Money) : SignedMoney :=
  Int.ofNat revenue - Int.ofNat totalCosts

/-- States the safety property captured by `profitAmount_le_revenue`. -/
theorem profitAmount_le_revenue (revenue totalCosts : Money) :
    profitAmount revenue totalCosts ≤ revenue := by
  unfold profitAmount
  exact Nat.sub_le revenue totalCosts

/-- If costs cover revenue, conservative natural-number profit is zero. -/
theorem profitAmount_eq_zero_of_revenue_le_costs
    (revenue totalCosts : Money) (h : revenue ≤ totalCosts) :
    profitAmount revenue totalCosts = 0 := by
  unfold profitAmount
  exact Nat.sub_eq_zero_of_le h

/-- States the safety property captured by `profitAmount_ge_minProfit`. -/
theorem profitAmount_ge_minProfit
    (revenue totalCosts minProfit : Money)
    (h : totalCosts + minProfit ≤ revenue) :
    minProfit ≤ profitAmount revenue totalCosts := by
  unfold profitAmount
  exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using h)

/-- States the safety property captured by `profitAmount_plus_costs_eq_revenue`. -/
theorem profitAmount_plus_costs_eq_revenue
    (revenue totalCosts : Money)
    (h : totalCosts ≤ revenue) :
    profitAmount revenue totalCosts + totalCosts = revenue := by
  unfold profitAmount
  exact Nat.sub_add_cancel h

/-- Signed profit/loss is non-negative exactly when costs do not exceed revenue. -/
theorem profitLossAmount_nonnegative_if_costs_le_revenue
    (revenue totalCosts : Money) (h : totalCosts ≤ revenue) :
    0 ≤ profitLossAmount revenue totalCosts := by
  unfold profitLossAmount
  exact sub_nonneg.mpr (Int.ofNat_le.mpr h)

/-- Signed profit/loss records an actual loss when costs exceed revenue. -/
theorem profitLossAmount_negative_if_revenue_lt_costs
    (revenue totalCosts : Money) (h : revenue < totalCosts) :
    profitLossAmount revenue totalCosts < 0 := by
  unfold profitLossAmount
  exact sub_neg.mpr (Int.ofNat_lt.mpr h)

/-- A signed profit/loss calculation satisfies the same minimum-profit guard. -/
theorem profitLossAmount_ge_minProfit
    (revenue totalCosts minProfit : Money)
    (h : totalCosts + minProfit ≤ revenue) :
    Int.ofNat minProfit ≤ profitLossAmount revenue totalCosts := by
  unfold profitLossAmount
  rw [le_sub_iff_add_le]
  have hNat : minProfit + totalCosts ≤ revenue := by
    simpa [Nat.add_comm] using h
  simpa using (Int.ofNat_le.mpr hNat)

/-- When revenue covers costs, signed profit/loss agrees with non-negative profit. -/
theorem profitLossAmount_eq_profitAmount_of_costs_le_revenue
    (revenue totalCosts : Money) (h : totalCosts ≤ revenue) :
    profitLossAmount revenue totalCosts = Int.ofNat (profitAmount revenue totalCosts) := by
  unfold profitLossAmount profitAmount
  exact (Int.natCast_sub h).symm


end CommerceTheory
