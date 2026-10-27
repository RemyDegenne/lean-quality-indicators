@[expose] public section

namespace Stafford38.Characteristic.ArtinianTriangularTrace

open Matrix

noncomputable section

universe u

variable {K : Type u} [Field K]

variable {n : ℕ}

/-- The matrix left after the maximal-ideal-adapted first-order calculation.
The order of both commutators is the order occurring in the published
calculation. -/
def adaptedFirstOrderMatrix
    (R Θ A B Γ : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  R + matrixCommutator Θ A + matrixCommutator B Γ

end
end Stafford38.Characteristic.ArtinianTriangularTrace
end
