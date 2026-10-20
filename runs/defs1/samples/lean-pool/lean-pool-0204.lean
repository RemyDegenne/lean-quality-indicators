@[expose] public section

open Finset

namespace Combinatorics.ArithmeticProgression

/-- The grids on which `A` has density at least `δ`. -/
noncomputable def denseGrids (δ : ℝ) (m n D : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (grids m n D).filter fun p ↦ δ * m ≤ #(indicesIn m A p)

end Combinatorics.ArithmeticProgression
end
