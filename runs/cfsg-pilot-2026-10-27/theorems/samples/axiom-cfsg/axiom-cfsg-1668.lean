public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section Data

variable {G : Type} [Group G] [Finite G]

theorem charTwo_inf_normalizer_of_radData {K R : Subgroup G} (hD : RadData ↥K) (hRK : R ≤ K)
    (hR2 : IsPGroup 2 ↥R) (hR : R ≠ ⊥)
    (hrad : pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) = R) :
    CharTwo (K ⊓ Subgroup.normalizer (R : Set G)) := by
  by_cases h : ∃ x ∈ K, x ≠ 1 ∧ Odd (orderOf x) ∧ R ≤ Subgroup.centralizer ({x} : Set G)
  swap
  · exact charTwo_inf_normalizer_of_no_odd_cent hrad fun x hxK hx1 hxo hRx =>
      h ⟨x, hxK, hx1, hxo, hRx⟩
  exfalso
  obtain ⟨x, hxK, hx1, hxo, hRx⟩ := h
  have hRcomm : ∀ r ∈ R, r * x = x * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRx hr)
  have hx'1 : (⟨x, hxK⟩ : ↥K) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hx'o : Odd (orderOf (⟨x, hxK⟩ : ↥K)) := by rwa [Subgroup.orderOf_mk]
  have h4 : Nat.card ↥R < 4 := by
    by_contra h4
    rcases exists_order_four_or_klein_of_pGroup hR2 (not_lt.mp h4) with
      ⟨u, huR, hu4⟩ | ⟨a, haR, b, hbR, ha1, hb1, hab, haa, hbb, hcab⟩
    · have hu4' : u * u * (u * u) = 1 := by
        have : u ^ 4 = 1 := hu4 ▸ pow_orderOf_eq_one u
        calc u * u * (u * u) = u ^ 4 := (pow_four_eq' u).symm
          _ = 1 := this
      have h := hD.odd_no4 ⟨x, hxK⟩ hx'1 hx'o ⟨u, hRK huR⟩ (Subtype.ext (hRcomm u huR))
        (Subtype.ext hu4')
      have huu : u * u = 1 := congrArg Subtype.val h
      have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact huu)
      rw [hu4] at this
      omega
    · exact hD.odd_noV ⟨x, hxK⟩ hx'1 hx'o ⟨a, hRK haR⟩ ⟨b, hRK hbR⟩
        (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
        (fun h => hab (congrArg Subtype.val h)) (Subtype.ext haa) (Subtype.ext hbb)
        (Subtype.ext hcab) (Subtype.ext (hRcomm a haR)) (Subtype.ext (hRcomm b hbR))
  have hcard : Nat.card ↥R = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
    have hk1 : k ≠ 0 := by
      rintro rfl
      exact hR (Subgroup.eq_bot_of_card_eq R (by rw [hk]; rfl))
    have hk2 : k < 2 := by
      by_contra hk2
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hk2)
      omega
    have hk3 : k = 1 := by omega
    rw [hk, hk3]
    norm_num
  obtain ⟨t, htR, ht1⟩ : ∃ t ∈ R, t ≠ 1 := by
    obtain ⟨⟨t, htR⟩, ht⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR
    exact ⟨t, htR, fun h => ht (Subtype.ext h)⟩
  have hto : orderOf t = 2 := by
    have hdvd : orderOf t ∣ 2 := by
      rw [← hcard, ← Subgroup.orderOf_mk t htR]
      exact orderOf_dvd_natCard (⟨t, htR⟩ : ↥R)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [hto, pow_two] at this
    exact this
  have hRel : ∀ r ∈ R, r = 1 ∨ r = t := by
    have hzp : Subgroup.zpowers t = R :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htR)
        (by rw [Nat.card_zpowers, hto, hcard])
    intro r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ hr)
    have hmod := zpow_mod_orderOf t k
    rw [hto] at hmod
    simp only [Nat.cast_ofNat] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← hmod, h]
      simp
    · right
      rw [← hmod, h]
      simp
  have htK : t ∈ K := hRK htR
  have hto' : orderOf (⟨t, htK⟩ : ↥K) = 2 := by rwa [Subgroup.orderOf_mk]
  obtain ⟨y, hy⟩ := hD.quat_ex ⟨t, htK⟩ hto'
  have hmul := hD.quat_mul_mem htK hto'
  set N : Subgroup G := K ⊓ Subgroup.normalizer (R : Set G) with hN
  have hQN : quatSubgroup K t htt hmul ≤ N := by
    intro z hz
    obtain ⟨hzK, hz⟩ := hz
    refine ⟨hzK, mem_normalizer_of_conj_mem fun f hf => ?_⟩
    have hzt : z * t = t * z := by
      rcases hz with h | h | h
      · rw [h, one_mul, mul_one]
      · rw [h]
      · exact (comm_of_sq h).symm
    have hzf : z * f = f * z := by
      rcases hRel f hf with h | h
      · rw [h, mul_one, one_mul]
      · rw [h]
        exact hzt
    have : z * f * z⁻¹ = f := by
      rw [hzf]
      group
    rw [this]
    exact hf
  have hNt : ∀ g ∈ N, g * t * g⁻¹ = t := by
    intro g hg
    have hgt : g * t * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg.2 t).mp htR
    rcases hRel _ hgt with h | h
    · exfalso
      apply ht1
      have h2 := congrArg (fun z => g⁻¹ * z * g) h
      have h3 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
      rw [h3]
      simpa using h2
    · exact h
  have hle := quatSubgroup_le_pCoreOf htt hmul inf_le_left hQN hNt
  rw [hrad] at hle
  have hyQ : (y : G) ∈ quatSubgroup K t htt hmul :=
    ⟨y.2, Or.inr (Or.inr (congrArg Subtype.val hy))⟩
  have hyt : (y : G) * y = t := congrArg Subtype.val hy
  rcases hRel _ (hle hyQ) with h | h
  · rw [h, one_mul] at hyt
    exact ht1 hyt.symm
  · rw [h, htt] at hyt
    exact ht1 hyt.symm

end Data
end CFSG.QuasithinUnique.Fin253
end
