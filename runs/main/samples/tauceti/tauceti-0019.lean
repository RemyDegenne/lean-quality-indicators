public section

open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

theorem loweringMatrix_def (i : Fin 4) : loweringMatrix i = weightTable.loweringMatrix i :=
  (rfl)

end TauCeti.D4Tripled
end
