public section

open Multiset

universe u

variable {α : Type*}

namespace Finset

attribute [local trans] Subset.trans Superset.trans

section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a : α}

theorem union_left_comm (s t u : Finset α) : s ∪ (t ∪ u) = t ∪ (s ∪ u) :=
  ext fun _ => by simp only [mem_union, or_left_comm]

end Lattice
end Finset
end
