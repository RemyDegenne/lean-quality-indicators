public section

open Multiset

universe u

variable {α : Type*}

namespace Finset

attribute [local trans] Subset.trans Superset.trans

section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a : α}

@[simp]
theorem union_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := sup_assoc _ _ _

end Lattice
end Finset
end
