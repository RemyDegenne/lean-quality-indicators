@[expose] public section

open Function Set

open Fin Matrix

variable {α : Type*}

variable [Preorder α] {n : ℕ}

variable {f : Fin (n + 1) → α} {a : α}

variable {n : ℕ}

/-- `Π i : Fin 2, α i` is order equivalent to `α 0 × α 1`. See also `OrderIso.finTwoArrowEquiv`
for a non-dependent version. -/
def OrderIso.piFinTwoIso (α : Fin 2 → Type*) [∀ i, Preorder (α i)] : (∀ i, α i) ≃o α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  map_rel_iff' := Iff.symm Fin.forall_fin_two

end
