public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem centralizer_d1KBar_le_d1X0_of_escape {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N)
    (hK : d1KBar p M N ≠ ⊥) :
    Subgroup.centralizer ((d1KBar p M N : Subgroup (N ⧸ primeComplementCore (G := N) p)) :
      Set (N ⧸ primeComplementCore (G := N) p)) ≤ d1X0 p M N := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  obtain ⟨R, hBR, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hB hBN
  have hRp : IsPGroup p (R.subgroupOf N) :=
    hR.isPGroup.comap_of_injective N.subtype N.subtype_injective
  set Rb : Sylow p (N ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O) with hRb
  have hRbeq : (Rb : Subgroup (N ⧸ O)) = (R.subgroupOf N).map π := by
    rw [hRb, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  obtain ⟨L₀, hL₀, hL₀X⟩ := exists_component_of_d1KBar_ne_bot hK
  refine centralizer_sup_components_le hp he.ne_two (primeComplementCore_quotient_eq_bot p) Rb
    (fun A hA hAe hAc h3 => ?_) (fun h2 => ?_) (d1KBar_normal_of_escape he hB hBN hK) hL₀ hL₀X
  · rw [hRbeq] at hA h3
    exact normalizer_le_d1X0_of_escape he hR.le hRM hR.isPGroup A hA hAe hAc h3
  ·
    have hRrank : CFSG.Open.pRank p R ≤ 2 := by
      rw [hRbeq, pRank_map_mk_eq_pRank_map_subtype hp O hO,
        Subgroup.map_subgroupOf_eq_of_le hR.le] at h2
      exact h2
    obtain ⟨-, -, h3 | ⟨E, hEB, hE, hEc, hΓ⟩⟩ := hB
    · exfalso
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
      have := h3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hBR)
      omega
    have hEN : E ≤ N := (hEB.trans hBR).trans hR.le
    have hEp : IsPGroup p (E.subgroupOf N) :=
      (hR.isPGroup.to_le (hEB.trans hBR)).comap_of_injective N.subtype N.subtype_injective
    refine ⟨(E.subgroupOf N).map π, ?_, CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
      (isElemAbelian_subgroupOf hE N) π, ?_, fun w hw hw1 => ?_⟩
    · rw [hRbeq]
      exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (hBR (hEB (Subgroup.mem_subgroupOf.mp hx)))
    · rw [card_map_mk_of_isPGroup hp O hO hEp, ← hEc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
    · obtain ⟨e, he', rfl⟩ := hw
      have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he'
      have hep : IsPGroup p (Subgroup.zpowers e) := hEp.to_le (Subgroup.zpowers_le.mpr he')
      have he1 : (e : G) ≠ 1 := by
        intro h
        apply hw1
        rw [show e = 1 from Subtype.ext h, map_one]
      have hNe : Subgroup.normalizer (Subgroup.zpowers (e : G) : Set G) ≤ M := by
        have hep' : (e : G) ^ p = 1 := hE.2 _ heE
        have hF1 : 1 ≤ CFSG.Open.pRank p (Subgroup.zpowers (e : G)) := by
          refine le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp _)
            ⟨Subgroup.zpowers (e : G), le_rfl, ⟨inferInstance, fun y hy => ?_⟩, ?_⟩
          · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hep', one_zpow]
          · rw [Nat.card_zpowers, orderOf_eq_prime hep' he1, pow_one]
        exact (le_sSup ⟨Subgroup.zpowers (e : G), Subgroup.zpowers_le.mpr heE, hF1, rfl⟩ :
          Subgroup.normalizer (Subgroup.zpowers (e : G) : Set G) ≤ GLBCore p 1 E).trans hΓ
      have hCN : Subgroup.centralizer (Subgroup.zpowers e : Set N) ≤ (N ⊓ M).subgroupOf N :=
        fun c hc => Subgroup.mem_subgroupOf.mpr ⟨c.property, hNe
          (Subgroup.centralizer_le_normalizer _ (by
            have := map_subtype_centralizer_le (Subgroup.zpowers e) ⟨c, hc, rfl⟩
            rwa [MonoidHom.map_zpowers] at this))⟩
      have hlift := Subgroup.map_mono (f := π) (comap_centralizer_map_le_sup hp O hO hep)
      rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O),
        Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, bot_sup_eq, MonoidHom.map_zpowers]
        at hlift
      exact hlift.trans (Subgroup.map_mono hCN)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
end
