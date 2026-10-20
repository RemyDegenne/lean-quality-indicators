@[expose] public section

open Set Function

open scoped symmDiff

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type x}

namespace Set

variable {s t : Set α}

section Infinite

variable [Infinite α]

lemma _root_.Finset.exists_notMem (s : Finset α) : ∃ a, a ∉ s := s.finite_toSet.exists_notMem

end Infinite
end Set
end
