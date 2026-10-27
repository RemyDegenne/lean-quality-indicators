public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s208a_mem_hSet_of_mem_calMOf (D : Data G) {L N : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hN : N ∈ calMOf (L ⊔ D.T)) : N ∈ hSet D.T D.M :=
  ⟨le_sup_right.trans hN.2,
    fun h => uc22p20i_not_le_M D hL (le_sup_left.trans (hN.2.trans h)),
    D.standing.charTwo N hN.1.1⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
end
