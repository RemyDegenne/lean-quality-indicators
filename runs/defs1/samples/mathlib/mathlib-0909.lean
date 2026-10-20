@[expose] public section

universe u v

namespace Fin

variable {m n : ℕ}

open Function

section Tuple

variable {α : Fin (n + 1) → Sort u} (x : α 0) (q : ∀ i, α i) (p : ∀ i : Fin n, α i.succ) (i : Fin n)
  (y : α i.succ) (z : α 0)

/-- Recurse on an `n+1`-tuple by splitting it into a single element and an `n`-tuple. -/
@[elab_as_elim]
def consCases {motive : (∀ i : Fin n.succ, α i) → Sort v} (cons : ∀ x₀ x, motive (Fin.cons x₀ x))
    (x : ∀ i : Fin n.succ, α i) : motive x :=
  _root_.cast (by rw [cons_self_tail]) <| cons (x 0) (tail x)

end Tuple
end Fin
end
