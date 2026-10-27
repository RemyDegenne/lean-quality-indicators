public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15
  CFSG.LocalAnalysis.AGL81TheoremC CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 Subgroup

variable {G : Type} [Group G] [Finite G]

namespace NineSetting

variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem ne_two (h : NineSetting G M p Q H E k) : p ≠ 2 :=
  QSet.ne_two_of_mem h.mem_Q

end NineSetting
end CFSG.LocalAnalysis.RankThreeUC.AGL81C
end
