public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

open scoped MatrixGroups Pointwise

section Specific

variable {G : Type} [Group G] [Finite G]

theorem stepA_e4_orderOf {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : orderOf (e 4) = 2 := by
  have h4 := (stepA_rels D.setup.lets).2.2.2.2
  have hne : e 4 ≠ 1 := by
    intro h
    apply stepA_e4_notMem D
    rw [h]
    exact Subgroup.one_mem _
  exact orderOf_eq_prime h4 hne

end Specific
end CFSG.GH74.QTGen4.Recog.G23.P7
end
