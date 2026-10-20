set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

section LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

namespace StableGL

theorem elementary_eq_ker_det_local (R : Type u) [CommRing R] [IsLocalRing R] :
    stableElementarySubgroup R = (det R).ker := by
  apply le_antisymm (elementary_le_ker_det R)
  intro g hg
  obtain ⟨n, x, rfl⟩ := exists_stage R g
  have hx : Matrix.GeneralLinearGroup.det x = 1 := by
    simpa only [MonoidHom.mem_ker, det_stage] using hg
  exact elementary_stage_le R n
    (Subgroup.mem_map_of_mem _ (mem_elementarySubgroup_iff_det_eq_one_local x |>.2 hx))

end StableGL
end LocalRing
end Matrix.GeneralLinearGroup
end
