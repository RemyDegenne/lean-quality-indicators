@[expose] public section

noncomputable section

namespace EulerCoefficientPath

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerMetricTransport EulerTransportDerivatives
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerLpCylinderRectangular

open scoped ContDiff BoundedContinuousFunction

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

local instance instCoefficientPathSmooth3 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance

local instance instCoefficientPathSmooth4 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

local instance instCoefficientPathSmooth5 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

local instance instCoefficientPathSmooth6 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

section Basic

variable (P : ℝ) [Fact (0 < P)]
  (A : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hA : ContDiff ℝ ∞ (translateCoefficientPath A))

/-- Smooth coefficient, bundling `coefficient`, `smooth`, `bound`, `norm_bound` and the required
compatibility proofs. -/
def smoothCoefficient (t : K) : SmoothCoefficient P where
  coefficient x := A t x.1
  smooth x := (coefficientOrbit_smooth A hA t).comp (contDiff_const.add contDiff_fst)
  bound := ‖A t‖₊
  norm_bound x := (A t).norm_coe_le_norm x.1
  firstBound := ‖iteratedFDeriv ℝ 1 (translateCoefficientPath A) 0‖₊
  norm_first x := by
    exact (norm_iteratedFDeriv_one (𝕜 := ℝ) _).symm.trans_le
      (cylinder_norm_iteratedFDeriv_le P A hA 1 t x 0)
  secondBound := ‖iteratedFDeriv ℝ 2 (translateCoefficientPath A) 0‖₊
  norm_second x y := by
    exact ((norm_iteratedFDeriv_one (𝕜 := ℝ) _).symm.trans norm_iteratedFDeriv_fderiv).trans_le
      (cylinder_norm_iteratedFDeriv_le P A hA 2 t x y)

end Basic
end EulerCoefficientPath
end
end
