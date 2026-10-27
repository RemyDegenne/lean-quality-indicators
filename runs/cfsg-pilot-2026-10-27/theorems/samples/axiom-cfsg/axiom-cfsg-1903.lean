public section

namespace CFSG.Quasithin

namespace S153EN8

section NormalTwo

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {U : Subgroup W}

theorem eq_bot_of_normal_pgroup (hN : ActsAsNaturalL2 L U) {S : Subgroup (MulAut W)} (hSL : S ≤ L)
    (hSn : ∀ l ∈ L, ∀ x ∈ S, l * x * l⁻¹ ∈ S) (hS2 : IsPGroup 2 S) : S = ⊥ := by
  have hcard : Nat.card L = 6 := (S1417.card_of_actsAsNaturalL2 hN).1
  have hsq : ∀ y ∈ S, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := hS2 ⟨y, hy⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf y ∣ 6 := by
      have := orderOf_dvd_natCard (⟨y, hSL hy⟩ : L)
      rw [Subgroup.orderOf_mk, hcard] at this
      exact this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
    have hj1 : j ≤ 1 := by
      by_contra hj'
      have h4 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      rw [← hj] at h4
      have := h4.trans h1
      omega
    apply orderOf_dvd_iff_pow_eq_one.1
    rw [hj]
    exact (pow_dvd_pow 2 hj1).trans (by simp)
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  have hx1' : x ≠ 1 := fun h => hx1 (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨c, hcL, hc3, hc1⟩ := S1417.exists_orderThree hN
  obtain ⟨e, -, -⟩ := hN
  have hz : x * (c * x * c⁻¹) ∈ S := S.mul_mem hx (hSn c hcL x hx)
  have hz2 := hsq _ hz
  have hLz : (⟨x, hSL hx⟩ * (⟨c, hcL⟩ * ⟨x, hSL hx⟩ * ⟨c, hcL⟩⁻¹) : L) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hz2
  have h1 := congrArg e hLz
  rw [map_pow, map_one, map_mul, map_mul, map_mul, map_inv] at h1
  refine sl2_no_normal_two (e ⟨x, hSL hx⟩) (e ⟨c, hcL⟩) ?_ ?_ ?_ ?_ h1
  · rw [← map_pow]
    have : (⟨x, hSL hx⟩ : L) ^ 2 = 1 := Subtype.ext (hsq x hx)
    rw [this, map_one]
  · intro h
    apply hx1'
    have h' : (⟨x, hSL hx⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h'
  · rw [← map_pow]
    have : (⟨c, hcL⟩ : L) ^ 3 = 1 := Subtype.ext hc3
    rw [this, map_one]
  · intro h
    apply hc1
    have h' : (⟨c, hcL⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h'

end NormalTwo
end S153EN8
end CFSG.Quasithin
end
