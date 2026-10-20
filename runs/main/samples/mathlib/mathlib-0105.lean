public section

universe u

variable {α : Type*}

namespace Finset

attribute [local trans] Subset.trans Superset.trans

section Lattice

variable [DecidableEq α] {s s₁ s₂ t : Finset α} {a b : α}

@[simp]
theorem union_empty (s : Finset α) : s ∪ ∅ = s :=
  ext fun x => mem_union.trans <| by simp

end Lattice
end Finset
end
