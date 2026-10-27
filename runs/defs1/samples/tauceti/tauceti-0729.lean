public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule Module

noncomputable section

section TorusConjugation

variable {A : Type*} [CommRing A] [Algebra (ZMod 2) A]

/-- The short-root weight torus as an invertible matrix. -/
noncomputable abbrev f4ShortRootWeightTorusGL (s : Fin 4 → Aˣ) :
    GL (Fin 26) A :=
  TauCeti.diagGL fun i => TauCeti.torusCharacter s (f4ShortRootWeight i)

end TorusConjugation
end
end TauCeti.DynkinType
end
