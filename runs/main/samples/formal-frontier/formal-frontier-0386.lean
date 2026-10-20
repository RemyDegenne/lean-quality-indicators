set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uR uS uT

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
  {R : Type uR} {S : Type uS} [Ring R] [Ring S]

theorem mapRingHom_elementarySubgroup_le (f : R →+* S) :
    (elementarySubgroup ι R).map (mapRingHom f) ≤ elementarySubgroup ι S := by
  apply Subgroup.map_le_iff_le_comap.mpr
  change Subgroup.closure _ ≤ _
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, j, hij, a, rfl⟩
  change mapRingHom f (elementaryUnit i j hij a) ∈ elementarySubgroup ι S
  rw [mapRingHom_elementaryUnit]
  exact elementaryUnit_mem i j hij (f a)

end Matrix.GeneralLinearGroup
end
