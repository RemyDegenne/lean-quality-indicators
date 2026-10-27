public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

variable {G : Type} [Group G] [Finite G]

theorem footeSixF_of_thm66F (h66 : Thm66F) : FooteSixF := by
  intro G _ _ _ _ hKP hG he M J hM hJ hJF
  obtain ⟨N, hN, hJN⟩ : ∃ N : Subgroup G, GLBIsMaxTwoLocal N ∧
      Subgroup.normalizer (J : Set G) ≤ N := by
    have h2l : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 J : Set G)) :=
      ⟨pCoreOf 2 J, pCoreOf_ne_bot_of_isFooteBlock hJ,
        CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J, rfl⟩
    obtain ⟨N, hN, hNN⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_isMaxTwoLocalSubgroup_le h2l
    exact ⟨N, hN, (normalizer_le_normalizer_pCoreOf J).trans hNN⟩
  exact footeSix_of_D1 hG hJ
    ⟨N, hN, hJN, isSubnormal_of_normalizer_le hG hKP he h66 hM hN hJ hJF hJN⟩

end CFSG.CGT.Foote82
end
