@[expose] public section

namespace BeyondBethe

open Complexity

/-- Rational data returned by a normalized regularized-Bethe optimizer. -/
structure RationalOptimizerOutput (n : ℕ) where
  /-- The rational matrix returned by the optimizer. -/
  matrix : Matrix (Fin n) (Fin n) ℚ
  /-- The optimizer's rational potential indexed by matrix rows. -/
  rowPotential : Fin n → ℚ
  /-- The optimizer's rational potential indexed by matrix columns. -/
  columnPotential : Fin n → ℚ

end BeyondBethe
end
