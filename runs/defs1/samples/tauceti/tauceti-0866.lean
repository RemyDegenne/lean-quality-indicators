public section

namespace TauCeti.SpecialLinear

open WithConv

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]

variable (n : ℕ)

/-- The determinant-one matrix of a point of `SLₙ` valued in its counit algebra. -/
noncomputable def counitPointsMulEquiv :
    WithConv (coordinateHopfAlgebra R n →ₐ[R]
        Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B) ≃*
      Matrix.SpecialLinearGroup (Fin n) B :=
  (Bialgebra.CounitAlgebra.pointsMulEquiv R (coordinateHopfAlgebra R n) B).trans
    (pointsMulEquiv (R := R) (A := B) n)

end TauCeti.SpecialLinear
end
