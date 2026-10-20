public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

open LieAlgebra TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The target index of each coordinate vector under the divided square of the `i`th raising
generator. Only the two short simple roots contribute, each moving the coordinate vector of the
negative of its root to that of the root itself. -/
@[expose] def raisingDividedSquareTarget : Fin 4 → Fin 26 → Fin 26 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 11, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 10, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]

end TauCeti.F4ShortRoot
end
