@[expose] public section

open Function MeasureTheory Set

open scoped ENNReal BigOperators

namespace QuadraticCarleson

namespace LacunaryMiddleOperator

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals

open CalderonZygmundLevelAtoms

open CanonicalScaleAtoms LacunaryMiddleRange LacunaryMiddleRangeSummation

open LacunaryLowSupport LacunaryVerySmallOperator PositiveEndpointOptimization

open LowKernelLevelSummation PositiveLowFullEstimate

open QuadraticHilbertMaximalMeasurable

noncomputable
section

theorem integrable_middleRangeInput
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (m : ℤ) :
    Integrable (middleRangeInput A f k B c m) := by
  unfold middleRangeInput
  exact integrable_finsetSum _ fun j _ ↦
    integrable_stoppingScaleLevelBadPart hf hfi j hAk

end
end LacunaryMiddleOperator
end QuadraticCarleson
end
