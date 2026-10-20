@[expose] public section

noncomputable section

open MeasureTheory Filter

open scoped NNReal ENNReal

variable {α 𝕜 𝕜' E F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

open MeasureTheory

section Composition

variable {g : E → F} {c : ℝ≥0}

namespace MeasureTheory.Lp

section LpToLpOfMeasureLeSMul

variable [NormedSpace ℝ E] {ν : Measure α} {c : ℝ≥0∞}

lemma coeFn_LpToLpOfMeasureLeSMul [Fact (1 ≤ p)] (hc : c ≠ ∞) (h : μ ≤ c • ν) (f : Lp E p ν) :
    LpToLpOfMeasureLeSMul hc h f =ᵐ[μ] f :=
  coeFn_LpToLpOfMeasureLeSMulₗ hc h f

end LpToLpOfMeasureLeSMul
end MeasureTheory.Lp
end Composition
end
end
