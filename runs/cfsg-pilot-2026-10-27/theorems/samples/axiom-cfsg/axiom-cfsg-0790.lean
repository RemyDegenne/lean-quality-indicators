public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers

open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D1IbCubeConfig.false {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}
    (hc : D1IbCubeConfig p P M H R Rbar K z) (hI : D1IbCubeInputs)
    (hShape : KFactSmallSylowShape) : False := by
  obtain ⟨L, hL⟩ := hc.phase.exists_weakSBlock hI.blocks.h84 hI.blocks.hD2
  have hRM := hc.phase.le_M
  have hzL := hc.mem_rPart_block hI.blocks hShape hI.orbits hL
  have hzbL := (mem_rPart hRM hc.elt.1).mp hzL
  rcases hc.lattice hShape hI.orbits inf_le_left (hc.isInvR_block hL) with hTL | ⟨-, h0, h1⟩
  · exact hc.false_of_plane hI hShape hL (inf_le_left.trans hTL) hzL
  by_cases hD : rPart M R (barM M L) ⊓ d1LiftX p H R K = ⊥
  · have hBL := h0 hD
    rcases hc.lattice hShape hI.orbits inf_le_left (hc.isInvR_cent hL) with hTC | ⟨-, h0C, h1C⟩
    · exact hc.false_of_fusion hShape hL hBL hzbL (inf_le_left.trans hTC)
    by_cases hDC : rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ⊓
        d1LiftX p H R K = ⊥
    · have hCz := h0C hDC
      have hC1 : rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) =
          ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).mpr fun b hb => ?_
        by_contra hb1
        exact hc.not_mem_cent hL ((Subgroup.zpowers_le.mpr hb)
          (mem_zpowers_of_mem_zpowers_of_prime hc.prime hc.elt.2.1 (hCz hb) hb1))
      exact hc.false_of_cyc_bot hI.blocks hShape hL hBL hzbL hC1
    · exact hc.false_of_fusion hShape hL hBL hzbL (h1C hDC)
  · exact hc.false_of_plane hI hShape hL (h1 hD) hzL

end CFSG.AGLEmbedding
end
