@[expose] public section

open CategoryTheory

namespace CategoryTheory.QuadrantProductTotal

universe u

variable {R : Type u} [Ring R]

/-- The horizontal source of the coordinate at `i`. -/
def horizontalIndex {k : ℤ} (i : Diag (k - 1)) : Diag k :=
  ⟨(i.1.1, i.1.2 + 1), by have hi := i.2; dsimp [Diag] at hi ⊢; omega⟩

end CategoryTheory.QuadrantProductTotal
end
