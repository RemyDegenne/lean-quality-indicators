public section

namespace CFSG.RankThree.PartTwo.Sec15.Read148Perf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem cubeComm_alternatingGroup (n : ℕ) (hn : 5 ≤ n) : CubeComm (alternatingGroup (Fin n)) :=
  have := Y4Core.isSimpleGroup_alternatingGroup n hn
  CubeComm.of_isSimpleGroup (Y4Core.three_dvd_card_alternatingGroup n (by omega))

end CFSG.RankThree.PartTwo.Sec15.Read148Perf
end
