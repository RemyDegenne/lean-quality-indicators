@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral Finset

open scoped ContDiff Topology

/-- Regularized solution, given by `Classical.choose ((regularizer n).exists_smooth
(regularizedTime A) (regularizedTime_pos A).le A hA)`. -/
def regularizedSolution (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) (n : ℕ) :
    RegularizedEvolution (regularizer n) (regularizedTime A) (regularizedTime_pos A).le :=
  Classical.choose ((regularizer n).exists_smooth (regularizedTime A) (regularizedTime_pos A).le A
      hA)

end EulerOrdinarySobolev
end
end
