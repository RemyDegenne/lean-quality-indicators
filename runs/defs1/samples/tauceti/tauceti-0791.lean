public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

variable (R : Type u) [CommRing R] {N : ℕ}

/-- The quotient-coordinate isomorphism underlying the identification of the relative
weight-unipotent quotient spectrum. -/
noncomputable def weightUnipotentInParabolicCoordinateIso (w : Fin N → ℤ) :
    weightUnipotentCoordinateHopfAlgebra R w ≅
      CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w) :=
  eqToIso (congrArg (CommHopfAlgCat.quotient (coordinateHopfAlgebra R N))
      (weightUnipotentInParabolicHopfIdeal_comapOfSurjective R w).symm) ≪≫
    CommHopfAlgCat.Hom.quotientIsoOfSurjective
      (weightParabolicCoordinateMap R w)
      (weightParabolicCoordinateMap_surjective R w)
      (weightUnipotentInParabolicHopfIdeal R w)

end TauCeti.GeneralLinear.Dynamic
end
