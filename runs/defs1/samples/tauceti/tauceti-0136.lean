public section

open LieAlgebra Matrix

namespace TauCeti.SpecialOrthogonal

universe u w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]

variable (n : ℕ)

/-- The tangent Lie algebra of `SOₙ` is the classical orthogonal Lie algebra, whenever `2` is
invertible in the coefficient algebra. -/
noncomputable def tangentLieEquivSo [Invertible (2 : B)] :
    Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B) ≃ₗ⁅B⁆
      LieAlgebra.Orthogonal.so (Fin n) B :=
  (HopfIdeal.quotientLieEquiv (B := B) (definingHopfIdeal R n)).trans
    ((GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) n).ofSubalgebras _ _
      (map_lieSubalgebra_definingHopfIdeal n))

end TauCeti.SpecialOrthogonal
end
