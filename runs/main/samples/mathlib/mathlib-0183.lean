@[expose] public section

variable {α : Type*}

namespace Multiset

section LocallyFiniteOrderTop

variable [Preorder α] [LocallyFiniteOrderTop α] {a x : α}

@[simp] lemma mem_Ici : x ∈ Ici a ↔ a ≤ x := by rw [Ici, ← Finset.mem_def, Finset.mem_Ici]

end LocallyFiniteOrderTop
end Multiset
end
