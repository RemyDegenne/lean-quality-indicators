public section

namespace CFSG.AGLEmbedding.FixedThree

open CFSG.Assembly.LowTwoRank

open CFSG.Open (IsComponentOf griessHopfMultiplier)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

open TauCeti

theorem kFactCompFixedThreeElt_of_families (hGA : CFSG.Open.GriessAllModelsStatement)
    (hOutS : ∀ s : SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (CFSGIndex.sporadic s).Group))
    (hSmall : OutSmallLie) (hLin : FixedThreeLinear) (hUni : FixedThreeUnitary)
    (hE6 : FixedThreeE6) : KFactCompFixedThreeElt := by
  intro X _ _ L hL hcat hZ h3 u hu3 huN huC
  have hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  change FixedThreeConclusion L u
  by_cases hcen : Subgroup.center ↥L = ⊥
  · have h3L : 3 ∣ Nat.card ↥L := by
      have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
      rw [Subgroup.card_eq_one.mpr hcen, mul_one] at hc
      rw [hc]
      exact h3
    exact conclusion_of_center_bot hcen h3L hu3 huN huC
  by_cases hin : ∃ a ∈ L, ∀ l ∈ L, u * l * u⁻¹ = a * l * a⁻¹
  · obtain ⟨a, haL, ha⟩ := hin
    exact conclusion_of_inner hZ hu3 huC haL ha
  push Not at hin
  have hout := three_dvd_card_outer_of_not_inner hperf hu3 huN hin
  have hZ3 : 3 ∣ Nat.card (Subgroup.center ↥L) := by
    have : Nontrivial ↥(Subgroup.center ↥L) := (Subgroup.nontrivial_iff_ne_bot _).2 hcen
    obtain ⟨n, hn, hcard⟩ := (hZ.nontrivial_iff_card).1 this
    rw [hcard]
    exact dvd_pow_self 3 hn.ne'
  have hM : 3 ∣ Nat.card (griessHopfMultiplier (↥L ⧸ Subgroup.center ↥L)) :=
    hZ3.trans (card_center_dvd_card_griessHopfMultiplier hperf (MulEquiv.refl _))
  obtain ⟨hnab⟩ : Nonempty (∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a) :=
    ⟨CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp =>
    obtain ⟨a, b, hab⟩ := hnab
    exfalso
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exfalso
    have h1 : 3 ∣ Nat.card (Outer (alternatingGroup (Fin n))) := by
      rw [← Nat.card_congr (equivalence e).toEquiv]
      exact hout
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn 3 Nat.prime_three
      (by norm_num) h1
  | sporadic s =>
    exfalso
    have h1 : 3 ∣ Nat.card (Outer (CFSGIndex.sporadic s).Group) := by
      rw [← Nat.card_congr (equivalence e).toEquiv]
      exact hout
    exact hOutS s 3 Nat.prime_three (by norm_num) h1
  | lie d =>
    rcases lieThree_of_index hGA d e hM with ⟨n, p, f, hm, hg⟩ | ⟨n, p, f, hm, hg⟩ |
      ⟨q, hv, rfl, hq⟩ | ⟨q, hv, rfl, hq⟩ | ⟨q, hv, rfl, hq⟩ | ⟨q, hv, rfl, hq⟩ | ⟨q, hv, rfl, hq⟩
    · exact hLin X L hL hZ hcen n p f hm hg u hu3 huN hin
    · exact hUni X L hL hZ hcen n p f hm hg u hu3 huN hin
    · exact hE6 X L hL hZ hcen (Or.inl ⟨q, hv, ⟨e⟩, hq⟩) u hu3 huN hin
    · exact hE6 X L hL hZ hcen (Or.inr ⟨q, hv, ⟨e⟩, hq⟩) u hu3 huN hin
    · exact (hSmall.twistedA _ q hv hq ⟨e⟩ hout).elim
    · exact (hSmall.b _ q hv hq ⟨e⟩ hout).elim
    · exact (hSmall.g _ q hv hq ⟨e⟩ hout).elim

end CFSG.AGLEmbedding.FixedThree
end
