@[expose] public section

noncomputable section

open Set Function

open scoped NNReal Topology ENNReal

namespace MeasureTheory

namespace OuterMeasure

section CaratheodoryMeasurable

universe u

variable {α : Type u} (m : OuterMeasure α)

attribute [local simp] Set.inter_comm Set.inter_left_comm Set.inter_assoc

variable {s s₁ s₂ : Set α}

lemma isCaratheodory_iUnion {s : ℕ → Set α} (h : ∀ i, m.IsCaratheodory (s i)) :
    m.IsCaratheodory (⋃ i, s i) := by
  rw [← iUnion_disjointed]
  exact m.isCaratheodory_iUnion_of_disjoint (m.isCaratheodory_disjointed h)
    (disjoint_disjointed _)

end CaratheodoryMeasurable
end OuterMeasure
end MeasureTheory
end
end
