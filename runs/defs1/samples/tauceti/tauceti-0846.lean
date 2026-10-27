public section

open CategoryTheory

namespace TauCeti

namespace AdditiveGroup

open AlgebraicGeometry Module MonObj MonoidalCategory

universe u

variable (R : Type u) [CommRing R]

/-- The commutative Hopf algebra representing the one-dimensional additive group. Its carrier is
`SymmetricAlgebra R R`, with primitive generator `SymmetricAlgebra.ι R R 1`. -/
noncomputable abbrev coordinateHopfAlgebra : CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.of R (SymmetricAlgebra R R)

end AdditiveGroup
end TauCeti
end
