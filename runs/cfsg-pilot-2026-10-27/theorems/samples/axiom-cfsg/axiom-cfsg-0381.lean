public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

namespace PbarMixedAux

theorem centralizer_singleton_of_zpowers {w y : G}
    (hw : w ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G)) :
    w ∈ Subgroup.centralizer {y} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((Subgroup.mem_centralizer_iff.mp hw) y (Subgroup.mem_zpowers y)).symm

end PbarMixedAux
end CFSG.GH74.QTGen4.Recog.G23.P7
end
