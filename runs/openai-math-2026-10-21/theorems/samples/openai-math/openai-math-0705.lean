namespace OAI

section

open Set Filter MeasureTheory Metric

open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Rearrangement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_norm_of_ae {p : ℝ → Prop} (hp : ∀ᵐ r : ℝ, p r) : ∀ᵐ x ∂μ, p ‖x‖ := by
  exact (ae_of_ae_map (by fun_prop)) ((map_norm_absolutelyContinuous μ).ae_le hp)

end CAT0Fillings.Rearrangement
end
end OAI
