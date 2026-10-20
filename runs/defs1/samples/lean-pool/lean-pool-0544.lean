@[expose] public section

noncomputable section

namespace EulerWeightedForcingTime

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution EulerFamilyNormTime
    EulerFiniteMetricEnergy

open scoped Topology

variable {A I H : Type*} [Fintype A] [Fintype I] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Multiplication by a continuous scalar time weight as a genuine Bochner operator. -/
def scalarTimeMultiplier (T : ℝ) (hT : 0 ≤ T) (w : C(Icc (0 : ℝ) T, ℝ)) : TimeLp T ℝ →L[ℝ] TimeLp T
    ℝ :=
  timeMultiplier T hT (⟨fun t => w t • ContinuousLinearMap.id ℝ ℝ,
    w.continuous.smul continuous_const⟩ : C(Icc (0 : ℝ) T, ℝ →L[ℝ] ℝ))

end EulerWeightedForcingTime
end
end
