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

/-- The genuine scale-sliced input `∑_{j∈S_{k,m}} b_{j,k}`. -/
def middleRangeInput
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (m : ℤ) (x : ℝ) : ℂ :=
  ∑ j ∈ S B c m, stoppingScaleLevelBadPart A f j k x

end
end LacunaryMiddleOperator
end QuadraticCarleson
end
