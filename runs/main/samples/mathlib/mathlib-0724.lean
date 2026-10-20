@[expose] public section

open MeasureTheory Set Function

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓧' : MeasurableSpace 𝓧'} [MeasurableSpace 𝓨]
  {π : Measure Θ} {P : Kernel Θ 𝓧} {ℓ : Θ → 𝓨 → ℝ≥0∞}

lemma riskIncrease_le_iInf' [Nonempty 𝓨] (hℓ : Measurable (uncurry ℓ)) [SFinite π] :
    riskIncrease ℓ P π ≤ ⨅ z : 𝓨, ∫⁻ θ, P θ univ * ℓ θ z ∂π :=
  riskIncrease_eq_iInf_sub' hℓ P π ▸ tsub_le_self

end ProbabilityTheory
end
