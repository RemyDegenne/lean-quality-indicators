public section

open AlgebraicGeometry CategoryTheory WithConv Matrix

open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic.IsotropicFlag

open GLSymplecticFin.IsotropicFlag

universe u v w

variable (R : Type u) [CommRing R] (m : ℕ)

/-- Coordinate restriction from the symplectic group to the isotropic flag subgroup. -/
noncomputable abbrev coordinateMap :
    Symplectic.coordinateHopfAlgebra R m ⟶ coordinateHopfAlgebra R m :=
  CommHopfAlgCat.mkQuotient (Symplectic.coordinateHopfAlgebra R m) (definingHopfIdeal R m)

end TauCeti.Symplectic.IsotropicFlag
end
