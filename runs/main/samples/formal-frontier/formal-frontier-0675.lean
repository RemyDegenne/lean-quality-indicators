@[expose] public section

open scoped commutatorElement

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

theorem elementary_gl (i j : Fin n) (hij : i < j) (a : R) :
    (elementary n R i j hij a).1 =
      Matrix.GeneralLinearGroup.elementaryUnit i j (ne_of_lt hij) a := rfl

end Matrix.UnitriangularGroup
end
