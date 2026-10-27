public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

open LieAlgebra TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

/-- The represented type-`F₄` Chevalley algebra: the image of the base-changed Serre
representation in the algebra of 26-by-26 matrices. -/
noncomputable def representedChevalleyAlgebra :
    LieSubalgebra R (Matrix (Fin 26) (Fin 26) R) :=
  (serreRepresentationBaseChange R).range

end TauCeti.F4ShortRoot
end
