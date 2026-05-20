import CommerceTheory.PostPurchase

namespace CommerceTheory

/-! ## 17. Forecasting, replenishment, and supplier risk -/

/-!
Forecasting separates demand estimates from automation decisions. Low-confidence
forecasts cannot trigger automatic replenishment, and supplier quality must meet
policy thresholds before it is approved.
-/

/-- Closed set of cases for `Confidence` in the commerce domain model. -/
inductive Confidence where
  | Low
  | Medium
  | High
deriving DecidableEq, Repr

/-- Computes or checks `confidenceAllowsAutoReplenish` using the validated data in this module. -/
def confidenceAllowsAutoReplenish : Confidence → Prop
  | Confidence.Low => False
  | Confidence.Medium => True
  | Confidence.High => True

/-- States the safety property captured by `lowConfidence_not_autoReplenish`. -/
theorem lowConfidence_not_autoReplenish :
    ¬ confidenceAllowsAutoReplenish Confidence.Low := by
  simp [confidenceAllowsAutoReplenish]

/-- Data shape for `DemandForecast`; proof fields record invariants when needed. -/
structure DemandForecast where
  sku : Sku
  expectedUnits : Quantity
  confidence : Confidence
  horizonDays : Days

/-- Data shape for `SupplierQualityMetrics`; proof fields record invariants when needed. -/
structure SupplierQualityMetrics where
  defectRateBps : Nat
  lateShipmentRateBps : Nat
  cancellationRateBps : Nat

/-- Data shape for `SupplierRiskPolicy`; proof fields record invariants when needed. -/
structure SupplierRiskPolicy where
  maxDefectRateBps : Nat
  maxLateShipmentRateBps : Nat
  maxCancellationRateBps : Nat

/-- Data shape for `ApprovedSupplierQuality`; proof fields record invariants when needed. -/
structure ApprovedSupplierQuality where
  supplier : DropshipSupplier
  metrics : SupplierQualityMetrics
  policy : SupplierRiskPolicy
  defect_ok : metrics.defectRateBps ≤ policy.maxDefectRateBps
  late_ok : metrics.lateShipmentRateBps ≤ policy.maxLateShipmentRateBps
  cancellation_ok : metrics.cancellationRateBps ≤ policy.maxCancellationRateBps

/-- States the safety property captured by `approvedSupplier_defect_ok`. -/
theorem approvedSupplier_defect_ok (a : ApprovedSupplierQuality) :
    a.metrics.defectRateBps ≤ a.policy.maxDefectRateBps := by
  exact a.defect_ok


end CommerceTheory
