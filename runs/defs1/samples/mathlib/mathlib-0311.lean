@[expose] public section

universe u v

namespace Fin

variable {m n : ℕ}

open Function

section InsertNth

variable {α : Fin (n + 1) → Sort*} {β : Sort*}

open Set

/-- Equivalence between tuples of length `n + 1` and pairs of an element and a tuple of length `n`
given by separating out the `p`-th element of the tuple.

This is `Fin.insertNth` as an `Equiv`. -/
@[simps symm_apply]
def insertNthEquiv (α : Fin (n + 1) → Type u) (p : Fin (n + 1)) :
    α p × (∀ i, α (p.succAbove i)) ≃ ∀ i, α i where
  toFun f := insertNth p f.1 f.2
  invFun f := (f p, removeNth p f)
  left_inv f := by ext <;> simp
  right_inv f := by simp

end InsertNth
end Fin
end
