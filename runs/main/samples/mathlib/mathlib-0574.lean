public section

open MeasureTheory Filter

open scoped ENNReal NNReal BoundedContinuousFunction Topology

namespace BoundedContinuousFunction

section NNRealValued

variable {X : Type*} [TopologicalSpace X]

variable [MeasurableSpace X]

lemma lintegral_le_edist_mul (f : X →ᵇ ℝ≥0) (μ : Measure X) :
    (∫⁻ x, f x ∂μ) ≤ edist 0 f * (μ Set.univ) :=
  le_trans (lintegral_mono (fun x ↦ ENNReal.coe_le_coe.mpr (f.apply_le_nndist_zero x))) (by simp)

end NNRealValued
end BoundedContinuousFunction
end
