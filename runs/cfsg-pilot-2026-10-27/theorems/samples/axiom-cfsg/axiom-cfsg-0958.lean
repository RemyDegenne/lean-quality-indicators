public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res5.L43

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434RemL43
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_centralizer_piL_mul_two {u : SL4} (hu : u ^ 3 = 1) :
    Nat.card (Subgroup.centralizer ({piL u} : Set PSL43)) * 2 =
      Nat.card (Subgroup.centralizer ({u} : Set SL4)) := by
  rw [← card_comap_piL, comap_centralizer_piL hu]

end CFSG.RankThree.PartTwo.Sec6.Res611Res5.L43
end
