@[expose] public section

open TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

section Inequalities

variable [ConditionallyCompleteLinearOrder ι] {u : ι → Ω → β} {s : Set β} {n i : ι} {ω : Ω}

theorem notMem_of_lt_hittingAfter {k : ι} (hk₁ : k < hittingAfter u s n ω) (hk₂ : n ≤ k) :
    u k ω ∉ s := by
  refine fun h ↦ not_le.2 hk₁ ?_
  rw [hittingAfter, ite_eq_left ⟨k, hk₂, h⟩]
  exact_mod_cast csInf_le (s := {i | n ≤ i ∧ u i ω ∈ s}) ⟨n, fun j hj => hj.1⟩ ⟨hk₂, h⟩

end Inequalities
end MeasureTheory
end
