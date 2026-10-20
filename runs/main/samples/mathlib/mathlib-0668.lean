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

theorem isCaratheodory_iff {s : Set α} :
    MeasurableSet[OuterMeasure.caratheodory m] s ↔ ∀ t, m t = m (t ∩ s) + m (t \ s) :=
  Iff.rfl

end CaratheodoryMeasurable
end OuterMeasure
end MeasureTheory
end
end
