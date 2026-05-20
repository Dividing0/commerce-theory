import CommerceTheory.Merchandising

namespace CommerceTheory

/-! ## 13. FX, tax, shipping zones, carrier rates, and reconciliation -/

/-!
Fulfillment finance adds exchange rates, tax calculations, carrier capacity, and
reconciliation tolerances. These definitions keep finance and shipping facts
explicit instead of hiding them inside external systems.
-/

/-- Data shape for `ExchangeRate`; proof fields record invariants when needed. -/
structure ExchangeRate where
  source : Currency
  target : Currency
  numerator : Nat
  denominator : Nat
  denominator_pos : 0 < denominator
  observedAt : Timestamp

/-- Computes or checks `fxQuoteFresh` using the validated data in this module. -/
def fxQuoteFresh (now maxAge : Timestamp) (r : ExchangeRate) : Prop :=
  r.observedAt ≤ now ∧ now - r.observedAt ≤ maxAge

/-- A fresh FX quote was not observed in the future relative to `now`. -/
theorem fxQuoteFresh_observedAt_le_now
    (now maxAge : Timestamp) (r : ExchangeRate) (h : fxQuoteFresh now maxAge r) :
    r.observedAt ≤ now := by
  exact h.left

/-- A fresh FX quote is within the permitted age window. -/
theorem fxQuoteFresh_age_le_maxAge
    (now maxAge : Timestamp) (r : ExchangeRate) (h : fxQuoteFresh now maxAge r) :
    now - r.observedAt ≤ maxAge := by
  exact h.right

/-- Computes or checks `convertMoneyFloor` using the validated data in this module. -/
def convertMoneyFloor (amount : Money) (rate : ExchangeRate) : Money :=
  amount * rate.numerator / rate.denominator

/-- Data shape for `TaxRate`; proof fields record invariants when needed. -/
structure TaxRate where
  bps : BasisPoints

/-- Data shape for `TaxCalculation`; proof fields record invariants when needed. -/
structure TaxCalculation where
  taxableAmount : Money
  tax : Money
  total : Money
  total_correct : total = taxableAmount + tax

/-- States the safety property captured by `tax_le_total`. -/
theorem tax_le_total (t : TaxCalculation) :
    t.tax ≤ t.total := by
  rw [t.total_correct]
  exact Nat.le_add_left t.tax t.taxableAmount

/-- Taxable amount is also bounded by the total including tax. -/
theorem taxableAmount_le_total (t : TaxCalculation) :
    t.taxableAmount ≤ t.total := by
  rw [t.total_correct]
  exact Nat.le_add_right t.taxableAmount t.tax

/-- Data shape for `ShippingZone`; proof fields record invariants when needed. -/
structure ShippingZone where
  id : Id
  name : String

/-- Data shape for `CarrierService`; proof fields record invariants when needed. -/
structure CarrierService where
  carrierId : Id
  zone : ShippingZone
  maxWeight : Weight
  baseCost : Money
  promisedDays : Days

/-- Data shape for `Package`; proof fields record invariants when needed. -/
structure Package where
  weight : Weight
  volume : Nat

/-- Data shape for `CarrierQuote`; proof fields record invariants when needed. -/
structure CarrierQuote where
  service : CarrierService
  package : Package
  price : Money
  package_weight_ok : package.weight ≤ service.maxWeight
  price_ge_cost : service.baseCost ≤ price

/-- States the safety property captured by `carrierQuote_weight_safe`. -/
theorem carrierQuote_weight_safe (q : CarrierQuote) :
    q.package.weight ≤ q.service.maxWeight := by
  exact q.package_weight_ok

/-- Carrier quote price covers the service's configured base cost. -/
theorem carrierQuote_price_covers_base_cost (q : CarrierQuote) :
    q.service.baseCost ≤ q.price := by
  exact q.price_ge_cost

/-- Computes or checks `absDiffNat` using the validated data in this module. -/
def absDiffNat (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

/-- The absolute difference between a value and itself is zero. -/
theorem absDiffNat_self (a : Nat) :
    absDiffNat a a = 0 := by
  unfold absDiffNat
  simp

/-- Natural absolute difference is symmetric. -/
theorem absDiffNat_comm (a b : Nat) :
    absDiffNat a b = absDiffNat b a := by
  unfold absDiffNat
  by_cases hab : a ≤ b
  · by_cases hba : b ≤ a
    · have hEq : a = b := Nat.le_antisymm hab hba
      subst b
      simp
    · simp [hab, hba]
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    simp [hab, hba]

/-- Data shape for `ReconciliationWithinTolerance`; proof fields record invariants when needed. -/
structure ReconciliationWithinTolerance where
  expected : Money
  actual : Money
  tolerance : Money
  diff_le_tolerance : absDiffNat expected actual ≤ tolerance

/-- States the safety property captured by `reconciliation_diff_safe`. -/
theorem reconciliation_diff_safe (r : ReconciliationWithinTolerance) :
    absDiffNat r.expected r.actual ≤ r.tolerance := by
  exact r.diff_le_tolerance

/-- Reconciliation tolerance is symmetric in expected and actual amounts. -/
theorem reconciliation_diff_safe_symm (r : ReconciliationWithinTolerance) :
    absDiffNat r.actual r.expected ≤ r.tolerance := by
  rw [absDiffNat_comm]
  exact r.diff_le_tolerance


end CommerceTheory
