public section

open AlgebraicGeometry CategoryTheory WithConv

open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic

universe u v w

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

section Functor

/-- The natural transformation of group-valued points for the negative long root `-2eᵢ`. -/
noncomputable def negativeLongRootSubgroupPointsMap (i : Fin m) :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) :=
  rootSubgroupPointsMap (.negativeLong i)

end Functor
end TauCeti.Symplectic
end
