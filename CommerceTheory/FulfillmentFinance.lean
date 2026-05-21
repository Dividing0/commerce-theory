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

/-- Convert money with an explicit rounding mode. -/
def convertMoneyRounded (mode : RoundingMode) (amount : Money) (rate : ExchangeRate) : Money :=
  roundMoney mode (amount * rate.numerator) rate.denominator

/-- Computes or checks `convertMoneyFloor` using the validated data in this module. -/
def convertMoneyFloor (amount : Money) (rate : ExchangeRate) : Money :=
  convertMoneyRounded RoundingMode.Floor amount rate

/-- Floor FX conversion uses the declared floor rounding mode. -/
theorem convertMoneyFloor_uses_floor_rounding (amount : Money) (rate : ExchangeRate) :
    convertMoneyFloor amount rate =
      convertMoneyRounded RoundingMode.Floor amount rate := by
  rfl

/-- Floor FX conversion decomposes exact scaled value into rounded units plus residual. -/
theorem convertMoneyFloor_decomposition (amount : Money) (rate : ExchangeRate) :
    convertMoneyFloor amount rate * rate.denominator +
      floorRoundingRemainder (amount * rate.numerator) rate.denominator =
        amount * rate.numerator := by
  unfold convertMoneyFloor convertMoneyRounded roundMoney
  exact floorRoundDiv_decomposition (amount * rate.numerator) rate.denominator

/-- FX floor-rounding error is bounded by one target minor unit. -/
theorem convertMoneyFloor_rounding_error_lt_one_minor_unit
    (amount : Money) (rate : ExchangeRate) :
    floorRoundingRemainder (amount * rate.numerator) rate.denominator <
      rate.denominator := by
  exact floorRoundingRemainder_lt_denominator
    (amount * rate.numerator) rate.denominator rate.denominator_pos

/-- FX line/item floor-rounding error is bounded by one target minor unit per line. -/
theorem fxLines_floor_rounding_error_le_one_minor_unit_per_line
    (amounts : List Money) (rate : ExchangeRate) :
    floorRoundedLinesRemainderTotal rate.denominator
        (amounts.map (fun amount => amount * rate.numerator)) ≤
      amounts.length * rate.denominator := by
  simpa using
    floorRoundedLinesRemainderTotal_le_one_minor_unit_per_line
      rate.denominator (amounts.map (fun amount => amount * rate.numerator))
      rate.denominator_pos

/-- Data shape for `TaxRate`; proof fields record invariants when needed. -/
structure TaxRate where
  bps : BasisPoints

/-- Apply a tax rate with an explicit rounding mode. -/
def taxAmountRounded (mode : RoundingMode) (rate : TaxRate) (taxableAmount : Money) : Money :=
  roundBpsAmount mode taxableAmount rate.bps

/-- Data shape for `TaxCalculation`; proof fields record invariants when needed. -/
structure TaxCalculation where
  taxableAmount : Money
  rate : TaxRate
  roundingMode : RoundingMode
  tax : Money
  total : Money
  tax_correct : tax = taxAmountRounded roundingMode rate taxableAmount
  total_correct : total = taxableAmount + tax

/-- Tax calculations expose the declared rounding mode used for the tax line. -/
theorem taxCalculation_uses_declared_rounding (t : TaxCalculation) :
    t.tax = taxAmountRounded t.roundingMode t.rate t.taxableAmount := by
  exact t.tax_correct

/-- Floor tax rounding error is bounded by one minor unit. -/
theorem tax_floor_rounding_error_lt_one_minor_unit
    (rate : TaxRate) (taxableAmount : Money) :
    floorRoundingRemainder (taxableAmount * rate.bps.value) 10000 < 10000 := by
  exact floorRoundingRemainder_lt_denominator
    (taxableAmount * rate.bps.value) 10000 (by norm_num)

/-- Tax line/item floor-rounding error is bounded by one minor unit per line. -/
theorem taxLines_floor_rounding_error_le_one_minor_unit_per_line
    (taxableAmounts : List Money) (rate : TaxRate) :
    floorRoundedLinesRemainderTotal 10000
        (taxableAmounts.map (fun amount => amount * rate.bps.value)) ≤
      taxableAmounts.length * 10000 := by
  simpa using
    floorRoundedLinesRemainderTotal_le_one_minor_unit_per_line
      10000 (taxableAmounts.map (fun amount => amount * rate.bps.value))
      (by norm_num)

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
