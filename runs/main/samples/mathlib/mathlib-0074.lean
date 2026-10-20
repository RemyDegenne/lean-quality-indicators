@[expose] public section

noncomputable section

open Set Function MeasurableSpace Filter ENNReal

open Filter hiding map

variable {α β δ : Type*} {ι : Sort*}

namespace MeasureTheory

scoped notation "Measure[" mα "] " α:arg => @Measure α mα

section

variable [MeasurableSpace α] {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}

theorem exists_measurable_superset_iff_measure_eq_zero :
    (∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = 0) ↔ μ s = 0 :=
  ⟨fun ⟨_t, hst, _, ht⟩ => measure_mono_null hst ht, exists_measurable_superset_of_null⟩

end
end MeasureTheory
end
end
