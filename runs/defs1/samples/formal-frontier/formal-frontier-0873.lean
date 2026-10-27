set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace Matrix

universe u

/-- The matrix of the specified right-linear row coordinates. Each column is
the image of a standard coordinate column. -/
noncomputable def rightRowCompletion (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    Matrix (Fin (m + 1)) (Fin n) R :=
  fun i j ↦ LinearEquiv.rightCoefficientRowCoordinates R a b hb e (Pi.single j 1) i

end Matrix
end
