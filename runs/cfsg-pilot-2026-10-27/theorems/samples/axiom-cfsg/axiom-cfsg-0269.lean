public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof168Res7

open Sec16.Proof165

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem one168_of_char2 (h : Sec17Std G A c L Y₀)
    (hst : StellmacherKP) (h146 : Item146 A (lB A))
    (h167 : Item167 A (lB A) c L) : One168 A := by
  intro V hV Y hY hVY
  obtain ⟨N, hYN, hN⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hY
  obtain ⟨hN1, -⟩ := Proof168.facts_of_mem_scriptY3Star h h146 h167 hV hN (hVY.trans hYN)
  refine ⟨N, hN1, fun Y₃ hY₃ hYY₃ => ?_⟩
  obtain ⟨I, hY₃I, hI⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hY₃
  exact hY₃I.trans (uniq h hst h146 h167 V hV Y hY hVY I hI N hN (hYY₃.trans hY₃I) hYN).le

end Proof168Res7
end CFSG.RankThree.PartTwo.Sec17
end
