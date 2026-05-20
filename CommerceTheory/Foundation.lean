import Mathlib

namespace CommerceTheory

/-! ## 0. Foundations -/

/-!
This module defines the shared vocabulary used by the rest of the theory.

Most numeric business quantities are modeled as `Nat` aliases. This keeps the
specification simple: money, quantities, weights, timestamps, and ids are all
non-negative by construction. More precise production code can refine these
types later, but the proofs here already capture the key safety properties.
-/

/-- Alias for `Money`, used to make business quantities read clearly. -/
abbrev Money := Nat
/-- Alias for `Quantity`, used to make business quantities read clearly. -/
abbrev Quantity := Nat
/-- Alias for `Weight`, used to make business quantities read clearly. -/
abbrev Weight := Nat
/-- Alias for `Timestamp`, used to make business quantities read clearly. -/
abbrev Timestamp := Nat
/-- Alias for `Days`, used to make business quantities read clearly. -/
abbrev Days := Nat
/-- Alias for `Id`, used to make business quantities read clearly. -/
abbrev Id := Nat

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

/-- States the safety property captured by `bps_mul_bound`. -/
theorem bps_mul_bound (bp : BasisPoints) (amount : Money) :
    amount * bp.value ≤ amount * 10000 := by
  exact Nat.mul_le_mul_left amount bp.value_le_10000

/-- Profit is modeled conservatively as natural subtraction, flooring at zero. -/
def profitAmount (revenue totalCosts : Money) : Money :=
  revenue - totalCosts

/-- States the safety property captured by `profitAmount_le_revenue`. -/
theorem profitAmount_le_revenue (revenue totalCosts : Money) :
    profitAmount revenue totalCosts ≤ revenue := by
  unfold profitAmount
  exact Nat.sub_le revenue totalCosts

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


end CommerceTheory
