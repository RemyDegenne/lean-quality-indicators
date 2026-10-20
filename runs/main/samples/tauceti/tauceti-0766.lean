public section

open scoped Matrix

namespace TauCeti.E6Minuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

@[simp]
theorem weightTable_reflection (i : Fin 6) :
    weightTable.reflection i = e6MinusculeReflection i :=
  (rfl)

end TauCeti.E6Minuscule
end
