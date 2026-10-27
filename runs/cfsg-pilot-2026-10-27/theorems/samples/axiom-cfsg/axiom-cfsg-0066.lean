public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

section ListCentre

variable {X : Type} [Group X] [Finite X]

theorem centre_barO2_eq_bot_of_pRank_three_aux_lie (hRank : LieOddRankChev) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T)
    (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) {d : TauCeti.ValidLieTypeIndex}
    (hdr : IsRankTwoPlus d.1) (hd : In1512 d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (h3 : CFSG.Open.pRank 3 L = 3) : Subgroup.center ↥(barO2 L) = ⊥ := by
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs hL
  obtain ⟨e'⟩ := e
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have h1 := pRank_lift_eq_three_of_excluded_aux_chev hRank hX hLs hL
    (centre_barO2_eq_bot_of_pRank_three_aux_classical hdr) ⟨e'⟩
  have hR : RankThreeList d.1 := ((mRank3_cases hdr _).2.2.1).1 (h1.symm.trans h3)
  obtain ⟨h2, h4⟩ := centre_barO2_eq_bot_of_pRank_three_aux_ne hR
  exact centre_eq_bot_of_in1512 hKSMOdd hKSMU4 hK hd h2 h4 ⟨eQ.trans e'⟩ (centre_barO2_odd hL.1)

end ListCentre
end CFSG.LocalAnalysis.RankThreeUC.S15
end
