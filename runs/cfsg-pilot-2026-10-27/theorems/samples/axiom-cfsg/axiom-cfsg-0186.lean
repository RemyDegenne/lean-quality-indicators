public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem KFactSetting.zjFrameGe {n : ℕ} {p : ℕ} {P : Sylow p G} {M D R T H V : Subgroup G}
    (hS : KFactSetting n G) (hD1 : TheoremD1 G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hp : p ∈ rankThreeSigmaA G)
    (hd : MaximalRelativePair p P M D R T) (hopt : IsOptimalRelPair p M D R T H V)
    (hfacts : OptimalRelPairFacts p M D H V) :
    ZJFrameGe p (primeComplementCore (G := H) p) (D.subgroupOf H) (V.subgroupOf H) := by
  have := hS.simple
  have hTwoLocal : IsTwoLocal H := hopt.pair.cand.twoLocal
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hopt.pair.cand.base_le
  have hVH : V ≤ H := hfacts.maximal.1
  have hV2 : IsPGroup 2 V := hfacts.maximal.2.1
  have hDV : D ≤ normalizer (V : Set G) := hfacts.maximal.2.2.1
  refine
    { pre := hS.obstruction.thompsonPreFrame hD1 hR h13 hp hd hopt hfacts
      exists_component := ?_
      sections := CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H
        (twoLocal_ne_top hS.nonab H hTwoLocal)
      three := fun hp5 Q hQ3 hDQ hfaith =>
        hS.obstruction.not_dvd_card_invariantTwoJoinIn_of_faithful hD1 hp hR h13 hd hopt hp5 hQ3
          hDQ hfaith
      charTwo := ?_
      sylow2 := ?_
      V_two := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
      D_norm := ?_
      core_le := ?_
      noncover := ?_
      exp := (hS.obstruction.normalizerExponent hD1 hR h13 hp hd).subgroupOf hDH }
  · obtain ⟨L, hL, -, -, -, hpL, hcat⟩ := hfacts.exists_component
    exact ⟨L, (CFSG.isComponent_iff_open L).mpr hL, hpL, hcat⟩
  · intro c hc
    have hcH : (c : G) ∈ H ⊓ centralizer (pCoreOf 2 H : Set G) := by
      refine ⟨c.2, ?_⟩
      show (c : G) ∈ centralizer (pCoreOf 2 H : Set G)
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hc y hy)
    obtain ⟨y, hy, hyc⟩ := hS.obstruction.charTwo H hTwoLocal hcH
    have : y = c := Subtype.ext hyc
    rwa [← this]
  · rw [← isSylowOf_map_subtype_iff H]
    exact hfacts.sylow
  · rw [← Subgroup.subgroupOf_normalizer_eq hVH]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hDV (Subgroup.mem_subgroupOf.mp hx))
  · intro x hx
    exact hfacts.pCore_le ⟨x, hx, rfl⟩
  · intro Z hZV hZ1 hZc hdvd
    have hZgV : Z.map H.subtype ≤ V := by
      rintro _ ⟨z, hz, rfl⟩
      exact hZV hz
    have hZg1 : Z.map H.subtype ≠ ⊥ := fun h => hZ1 (eq_bot_iff.mpr fun z hz => by
      have : (z : G) ∈ (⊥ : Subgroup G) := h ▸ ⟨z, hz, rfl⟩
      exact Subtype.ext (Subgroup.mem_bot.mp this))
    refine hfacts.not_dvd _ hZgV hZg1 (zjp_normalizer_le hVH hZV hZc) (hdvd.trans ?_)
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact Subgroup.card_dvd_of_le (zjp_join_le hDH Z)

end CFSG.LocalAnalysis.RankFourTheoremC
end
