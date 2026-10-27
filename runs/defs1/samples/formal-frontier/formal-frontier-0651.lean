@[expose] public section

open CategoryTheory

namespace CategoryTheory.QuadrantProductTotal

universe u

variable {R : Type u} [Ring R]

/-- Horizontal source of a coordinate in a native differential. -/
def nextHorizontalIndex (i j : ℤ) (h : j = i - 1) (t : Diag j) : Diag i :=
  ⟨(t.1.1, t.1.2 + 1), by have ht := t.2; dsimp [Diag] at ht ⊢; omega⟩

end CategoryTheory.QuadrantProductTotal
end
