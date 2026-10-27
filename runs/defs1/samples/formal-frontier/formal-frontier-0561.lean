public section

open scoped commutatorElement

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

/-- The infinite descending central series, starting at the entire point group. -/
def descendingSeries (t : ℕ) : Subgroup (Matrix.UnitriangularGroup (Fin n) R) :=
  superdiagonalSubgroup n R (t + 1)

end Matrix.UnitriangularGroup
end
