public section

open WithConv

namespace TauCeti.SpecialLinear.Borel

universe u

noncomputable section

variable (R : Type u) [CommRing R]

/-- The tautological point of the standard Borel in its own coordinate algebra. -/
def tautologicalPoint : SL2Borel (coordinateHopfAlgebra R) :=
  pointsMulEquiv (R := R) (A := coordinateHopfAlgebra R)
    (toConv (AlgHom.id R (coordinateHopfAlgebra R)))

end
end TauCeti.SpecialLinear.Borel
end
