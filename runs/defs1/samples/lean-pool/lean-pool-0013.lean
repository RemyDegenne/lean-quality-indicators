@[expose] public section

namespace BeyondBethe

open Complexity

/-- Evaluates the raw directed negative-objective summand using matrix coefficient `A i j` and
the corresponding affine entry of `y`. -/
def rawDirectedBetheObjectiveCoordinate {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) : RawRat :=
  rawDirectedNegativeObjectiveCoordinateLower tau (A i j)
    (betheAffineMatrixQ y i j) p

end BeyondBethe
end
