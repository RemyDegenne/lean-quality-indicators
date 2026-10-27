@[expose] public section

open Function

namespace YoungDiagram

section Columns

/-- The `j`-th column of a Young diagram consists of the cells whose second coordinate is `j`. -/
def col (μ : YoungDiagram) (j : ℕ) : Finset (ℕ × ℕ) :=
  μ.cells.filter fun c => c.snd = j

end Columns
end YoungDiagram
end
