@[expose] public section

open scoped Finset

namespace Equiv.Perm

open List (Vector)

open Equiv List Multiset

variable {α : Type*} [Fintype α]

namespace IsThreeCycle

variable [DecidableEq α] {σ : Perm α}

theorem card_support (h : IsThreeCycle σ) : #σ.support = 3 := by
  rw [← sum_cycleType, h.cycleType, Multiset.sum_singleton]

end IsThreeCycle
end Equiv.Perm
end
