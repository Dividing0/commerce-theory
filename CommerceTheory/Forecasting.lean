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

/-- Medium-confidence forecasts are permitted to trigger replenishment automation. -/
theorem mediumConfidence_allows_autoReplenish :
    confidenceAllowsAutoReplenish Confidence.Medium := by
  simp [confidenceAllowsAutoReplenish]

/-- High-confidence forecasts are permitted to trigger replenishment automation. -/
theorem highConfidence_allows_autoReplenish :
    confidenceAllowsAutoReplenish Confidence.High := by
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

/-- Approved suppliers meet the late-shipment threshold. -/
theorem approvedSupplier_lateShipment_ok (a : ApprovedSupplierQuality) :
    a.metrics.lateShipmentRateBps ≤ a.policy.maxLateShipmentRateBps := by
  exact a.late_ok

/-- Approved suppliers meet the cancellation-rate threshold. -/
theorem approvedSupplier_cancellation_ok (a : ApprovedSupplierQuality) :
    a.metrics.cancellationRateBps ≤ a.policy.maxCancellationRateBps := by
  exact a.cancellation_ok

/-- Compact reusable form of all supplier-quality threshold checks. -/
theorem approvedSupplier_quality_ok (a : ApprovedSupplierQuality) :
    a.metrics.defectRateBps ≤ a.policy.maxDefectRateBps ∧
      a.metrics.lateShipmentRateBps ≤ a.policy.maxLateShipmentRateBps ∧
      a.metrics.cancellationRateBps ≤ a.policy.maxCancellationRateBps := by
  exact ⟨a.defect_ok, a.late_ok, a.cancellation_ok⟩


end CommerceTheory
