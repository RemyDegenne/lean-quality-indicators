@[expose] public section

noncomputable section

open ENNReal Filter MeasureTheory NNReal Set TopologicalSpace

open scoped Topology

variable {α β γ δ ε ε' : Type*} {m : MeasurableSpace α} {μ ν : Measure α} [MeasurableSpace δ]

variable [NormedAddCommGroup β] [NormedAddCommGroup γ]
  [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']

namespace MeasureTheory

scoped notation "Integrable[" mα "]" => @Integrable _ _ _ _ mα

theorem ofReal_toReal_ae_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x < ∞) :
    (fun x => ENNReal.ofReal (f x).toReal) =ᵐ[μ] f := by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, ofReal_toReal, Ne, not_false_iff]

end MeasureTheory
end
end
