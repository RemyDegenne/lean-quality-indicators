public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem step156CQA5DFaith_of_o2
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142AllS14)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h153 : Item153Main A (lB A)) (hO2 : Step156CQA5DO2 A (lB A)) :
    Step156CQA5DFaith A (lB A) := by
  intro Y hY hY5 c₀ L₀ d X₁ D hΩ hLN hX5 hYX hfaith
  obtain ⟨hd, hc⟩ :=
    pCoreOf_le_centralizer_of_data156 h134 h48 h142 h h153 hY hY5 D hΩ hX5 hYX hfaith
  exact ⟨hd, hO2 Y hY hY5 c₀ L₀ d X₁ D hΩ hLN hX5 hYX hd hc⟩

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
end
