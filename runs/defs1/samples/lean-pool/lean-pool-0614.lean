@[expose] public section

namespace BGS.Markoff

open Finset

open BGS.FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Original-coordinate punctured Markoff points whose third coordinate vanishes. -/
def puncturedMarkoffThirdCoordinateZero (R : Type*) [CommRing R] :
    Set (PuncturedMarkoffSurface R) :=
  {x | x.1.1.x3 = 0}

end BGS.Markoff
end
