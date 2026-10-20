public section

open scoped commutatorElement

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

theorem nilpotencyClass_le :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin n) R) ≤ n - 1 := by
  apply (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le).mp
  apply le_antisymm _ bot_le
  calc
    Subgroup.lowerCentralSeries
        (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)) (n - 1) ≤
        descendingSeries n R (n - 1) :=
      Subgroup.descending_central_series_ge_lower (descendingSeries n R)
        (descendingSeries_isDescendingCentralSeries n R) (n - 1)
    _ = ⊥ := descendingSeries_end n R

end Matrix.UnitriangularGroup
end
