open CFSG

open scoped MatrixGroups Pointwise TensorProduct commutatorElement IsMulCommutative

section

variable {G : Type*} [Group G]

public theorem CFSG.thompsonSubgroup_eq_of_le [Finite G]
    {P R : Subgroup G} (hR_le_P : R ≤ P)
    (hJP_le_R : thompsonSubgroup (G := G) P ≤ R) :
    thompsonSubgroup (G := G) R = thompsonSubgroup (G := G) P := by
  apply le_antisymm
  · obtain ⟨A, hA⟩ := thompsonAbelianSubgroups_nonempty (G := G) P
    exact
      thompsonSubgroup_le_of_mem_thompsonAbelianSubgroups (G := G) hR_le_P hA
        ((le_sSup hA).trans hJP_le_R)
  · refine sSup_le ?_
    intro A hA
    exact
      le_sSup <|
        thompsonAbelianSubgroups_mem_of_le (G := G) hR_le_P hA
          ((le_sSup hA).trans hJP_le_R)

end
