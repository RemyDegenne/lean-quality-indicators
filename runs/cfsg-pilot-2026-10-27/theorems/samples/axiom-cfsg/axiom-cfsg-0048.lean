public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l2_type_facts {C K : Subgroup G} (hKC : K ≤ C) (hK : IsPComponent 2 (K.subgroupOf C))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p f) :
    (∀ x ∈ K, x * x = 1 → x ∈ zStarIn K → x = 1) ∧ pRank 2 ↥K = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K) := isSimpleGroup_of_lieModel_psl_two h
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K C hKC).mp hK
  obtain ⟨-, -, a, b, hab⟩ := id hq
  have hnab : ∃ x y : K ⧸ pPrimeCore 2 K, x * y ≠ y * x := by
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h' => hab (by rw [← QuotientGroup.mk_mul, h', QuotientGroup.mk_mul])⟩
  have hcen : center (K ⧸ pPrimeCore 2 K) = ⊥ := by
    rcases (inferInstance : (center (K ⧸ pPrimeCore 2 K)).Normal).eq_bot_or_eq_top with h1 | h1
    · exact h1
    · obtain ⟨x, y, hxy⟩ := hnab
      exact absurd ((mem_center_iff.mp (h1 ▸ mem_top x)) y).symm hxy
  refine ⟨fun x hxK hx2 hxZ => ?_, ?_⟩
  · obtain ⟨x', hx', rfl⟩ := hxZ
    rw [Sol78.fusionZStar_eq_comap, SetLike.mem_coe, mem_comap, hcen, mem_bot,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    have hodd : Odd (orderOf x') :=
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
        (Subgroup.orderOf_dvd_natCard _ hx')
    have h2 : orderOf x' ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]
      exact Subtype.ext hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
    · rw [orderOf_eq_one_iff] at h3
      rw [h3]
      rfl
    · rw [h3] at hodd
      exact absurd hodd (by decide)
  · have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥K) := by
      intro hd
      exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
        (even_iff_two_dvd.mpr hd)
    rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hodd]
    refine le_antisymm ?_
      (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq
        (by rw [hcen, card_bot]; exact odd_one))
    obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := FooteLit.statedClassicalModel_of_lieModel_psl_two h
    have hdih : GorensteinWalter.HasDihedralSylowTwo
        (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 F)) :=
      OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv
        (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
        (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
          ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hcard⟩)
    exact FooteLit.pRank_le_two_of_hasDihedralSylowTwo
      (OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv e hdih)

end CFSG.ComponentClassification.GrSLit.GrS5
end
