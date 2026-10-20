@[expose] public section

open Function MeasureTheory Set

open scoped ENNReal

namespace QuadraticCarleson

namespace LacunaryVerySmallOperator

open CalderonZygmundLevelAtoms LacunaryLowSupport

open LowKernelLevelSummation LacunaryVerySmallRange

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals

open CanonicalScaleAtoms

open PositiveLowFullEstimate

open PositiveHighHeightEstimate

open PositiveEndpointOptimization

/-- Pointwise norm of the genuine low-kernel action on the canonical
scale-sliced bad part `b_{j,k}`. -/
noncomputable def canonicalScaleLowActionEnorm
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B : ℕ) (m j : ℤ) (x : ℝ) : ENNReal :=
    ‖∫ y, paperLowCZKernel
        (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
      stoppingScaleLevelBadPart A f j k y‖ₑ

end LacunaryVerySmallOperator
end QuadraticCarleson
end
