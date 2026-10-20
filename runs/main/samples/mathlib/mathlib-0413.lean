@[expose] public section

noncomputable section

open ENNReal Filter MeasureTheory NNReal Set TopologicalSpace

open scoped Topology

variable {α β γ δ ε ε' : Type*} {m : MeasurableSpace α} {μ ν : Measure α} [MeasurableSpace δ]

variable [NormedAddCommGroup β] [NormedAddCommGroup γ]
  [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']

namespace MeasureTheory

scoped notation "Integrable[" mα "]" => @Integrable _ _ _ _ mα

lemma integrable_add_iff_of_nonneg {f g : α → ℝ} (h_meas : AEStronglyMeasurable f μ)
    (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ :=
  ⟨fun h ↦ ⟨integrable_left_of_integrable_add_of_nonneg h_meas hf hg h,
    integrable_right_of_integrable_add_of_nonneg h_meas hf hg h⟩, fun ⟨hf, hg⟩ ↦ hf.add hg⟩

end MeasureTheory
end
end
