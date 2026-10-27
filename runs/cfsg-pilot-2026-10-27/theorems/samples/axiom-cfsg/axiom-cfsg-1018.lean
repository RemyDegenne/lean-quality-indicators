public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2

open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

variable {G : Type} [Group G] [Finite G]

theorem agl81ElevenElevenParabolicGen_of_na (hC : AGL81TenThreeThreeCasesCfg G)
    (hK : KFactParabolicIrredCentralNA) (h10C : AGL81TenOneCZero G)
    (h91 : AGL81TenNineOneCfg G) : AGL81ElevenElevenParabolicGen G := by
  intro hS p P M H Q K hd hlist hrk hnc L hL hLn hAJ hNA hirr hodd
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hp : p.Prime := hesc.prime
  have hp2 : p ≠ 2 := hesc.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  set A := d1LiftX p H Q K with hAdef
  have hAQ : A ≤ Q := d1LiftX_le p H Q K
  have hAH : A ≤ H := hAQ.trans hd.le_H
  have hAM : A ≤ M := hAQ.trans hd.base.1
  have hA3 : IsPGroup p A := hd.base.2.1.to_le hAQ
  have hZ : ∀ k : K, (∀ k' : K, k * k' = k' * k) → k = 1 := by
    intro k hk
    by_contra hk1
    have hcen : Subgroup.center ↥K = ⊤ := by
      haveI := hlist.1
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
      · exfalso
        apply hk1
        have : k ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.mpr fun g => (hk g).symm
        rw [h] at this
        exact Subgroup.mem_bot.mp this
      · exact h
    letI : CommGroup ↥K :=
      { (inferInstance : Group ↥K) with
        mul_comm := fun a b => by
          have := Subgroup.mem_center_iff.mp (hcen ▸ Subgroup.mem_top a) b
          exact this.symm }
    haveI := hlist.1
    have hprime := IsSimpleGroup.prime_card (α := ↥K)
    obtain ⟨E, hEK, hE, hEc⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp hrk
    have hdvd : p ^ 2 ∣ Nat.card K := hEc ▸ Subgroup.card_dvd_of_le hEK
    have h1 : p ∣ Nat.card K := (dvd_pow_self p two_ne_zero).trans hdvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p h1) with h | h
    · exact hp.ne_one h
    · rw [← h] at hdvd
      have := Nat.le_of_dvd hp.pos hdvd
      nlinarith [hp.two_le]
  obtain ⟨-, S, hSA, ⟨e⟩⟩ := OtherCfg.d1LiftX_facts_gen hd hZ
  have hA2 : 2 ≤ Open.pRank p A := (OtherCfg.pRank_eq_of_sylow_equiv S e).symm ▸ hrk
  exact commutator_le_of_cases_na hK hp hp2 hL hLn (pRank_le_three_of_escape hS hd)
    (le_inf hAH hAM) hA3 (not_isCyclic_of_two_le_pRank hp hA2)
    (h10C hS p P M H Q K hd L hL (h91 hS p P M H Q K hd L hL)) hAJ hNA hirr
    fun b hb => hC hS p P M H Q K hd L hL hLn b ⟨hAH hb, hAM hb⟩
      (odd_orderOf_of_isPGroup hp hp2 hA3 hb) (hAJ b hb)

end CFSG.LocalAnalysis.RankThreeTheoremC
end
