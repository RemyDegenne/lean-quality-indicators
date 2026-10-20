public section

open scoped commutatorElement

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

theorem superdiagonalSubgroup_one : superdiagonalSubgroup n R 1 = ⊤ := by
  apply le_antisymm le_top
  intro g _
  exact hasSupport_sub_one n R g

end Matrix.UnitriangularGroup
end
