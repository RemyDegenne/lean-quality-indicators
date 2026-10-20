@[expose] public section

noncomputable section

open Set Filter TopologicalSpace MeasureTheory Function

open scoped Topology Interval Filter ENNReal MeasureTheory

variable {α β ε ε' E : Type*} {mα : MeasurableSpace α}

namespace MeasureTheory

section NormedAddCommGroup

variable [NormedAddCommGroup E] {f g : α → ε} {s t : Set α} {μ ν : Measure α}
  [TopologicalSpace ε] [ContinuousENorm ε]

variable [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

@[simp]
theorem integrableOn_finset_iUnion [PseudoMetrizableSpace ε] {s : Finset β} {t : β → Set α} :
    IntegrableOn f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, IntegrableOn f (t i) μ :=
  integrableOn_finite_biUnion s.finite_toSet

end NormedAddCommGroup
end MeasureTheory
end
end
