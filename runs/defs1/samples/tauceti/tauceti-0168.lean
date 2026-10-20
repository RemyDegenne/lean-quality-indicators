public section

namespace TauCeti.DynkinType

open Function

open scoped _root_.Matrix

/-- The special permutation of the root indices of the pinned type `F₄` datum. -/
def f4SpecialIsogenyIndexEquiv : Equiv.Perm (Fin 48) :=
  f4SpecialIsogenyIndex_involutive.toPerm _

end TauCeti.DynkinType
end
