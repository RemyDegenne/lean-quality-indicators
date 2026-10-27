public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7.VL

variable {G : Type} [Group G]

theorem sat_U_iff {ρ : Fin 5 → G} : SatWords vertexBaseU ρ ↔
    SatWords (relCommon ++ relTail) ρ ∧ FreeGroup.lift ρ (FreeGroup.mk hardU) = 1 := by
  rw [baseU_eq, satWords_append, satWords_singleton]

end CFSG.GH74.QTGen4.Recog.G23.P7.VL
end
