public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Sixteen21

theorem one_le_pRank_of_case2 {D : Data G} (h1217 : R1217 D) (hSg : UC6S846.SigmaStd D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_2 D V₀ V hV L) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank 7 (D.M ⊓ centralizer ({v} : Set G)) := by
  have h7 : 7 ∈ D.sig := by rw [hc.2.2.2]; exact Set.mem_singleton 7
  exact one_le_pRank_of_not_dvd_mbar hV hS.setting.hyp16 (p := 7) (k := 3) (by norm_num)
    (by norm_num) (D.sig_rank 7 h7) (hSg.three_le 7 h7)
    (c23_not_dvd_card_mbar_case2 D h1217 hS hc)

end Sixteen21
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
