@[expose] public section

open CategoryTheory

namespace CategoryTheory.QuadrantProductTotal

universe u

variable {R : Type u} [Ring R]

/-- Enumerate the primitive coordinates corresponding to a target diagonal. -/
abbrev primitiveIndex (k : ℤ) (n : ℕ) : Diag (k + 1) :=
  ⟨(firstRow k + n, firstColumn k + n + 1), by
    dsimp [Diag, firstRow, firstColumn]
    omega⟩

end CategoryTheory.QuadrantProductTotal
end
