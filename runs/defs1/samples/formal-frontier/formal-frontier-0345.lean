@[expose] public section

open CategoryTheory

namespace CategoryTheory.QuadrantProductTotal

universe u

variable {R : Type u} [Ring R]

/-- Indices `(r,p)` on the integral diagonal `p-r=k`. -/
abbrev Diag (k : ℤ) := {pr : ℕ × ℕ // (pr.2 : ℤ) - (pr.1 : ℤ) = k}

end CategoryTheory.QuadrantProductTotal
end
