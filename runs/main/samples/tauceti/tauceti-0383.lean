public section

open IntermediateField Polynomial

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K]

theorem toZModPow_three_localCyclotomicCharacter_eq_one_or_eq_three [NeZero (2 : K)] {s : K}
    (hs : s ^ 2 = -2) (σ : Field.absoluteGaloisGroup K) :
    PadicInt.toZModPow 3 (localCyclotomicCharacter 2 K σ : ℤ_[2]) = 1 ∨
      PadicInt.toZModPow 3 (localCyclotomicCharacter 2 K σ : ℤ_[2]) = 3 := by
  have h2 : (2 : AlgebraicClosure K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (AlgebraicClosure K)) 2]
    exact (_root_.map_ne_zero _).2 (NeZero.ne 2)
  have : NeZero ((2 ^ 3 : ℕ) : AlgebraicClosure K) :=
    ⟨by rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_ne_zero 3 h2⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure K) (2 ^ 3)
  have h4 : ξ ^ 4 = -1 :=
    (hξ.pow_of_dvd (by norm_num) (by norm_num : 4 ∣ 2 ^ 3)).eq_neg_one_of_two_right
  -- `ξ + ξ ^ 3` is a square root of `-2`, so it is `±s` and every automorphism fixes it.
  have ht2 : (ξ + ξ ^ 3) ^ 2 = -2 := by linear_combination (ξ ^ 2 + 2) * h4
  have hfix : σ.toRingEquiv (ξ + ξ ^ 3) = ξ + ξ ^ 3 := by
    have hst : (algebraMap K (AlgebraicClosure K) s) ^ 2 = (ξ + ξ ^ 3) ^ 2 := by
      rw [← map_pow, hs, ht2, map_neg, map_ofNat]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hst with h | h
    · rw [← h]
      exact σ.commutes s
    · rw [show ξ + ξ ^ 3 = -algebraMap K _ s by rw [h, neg_neg], map_neg]
      exact congrArg _ (σ.commutes s)
  -- `σ` raises `ξ` to the power `x.val`, an odd residue modulo `8`.
  have hspec := cyclotomicCharacter.spec 2 (n := 3) σ.toRingEquiv ξ hξ.pow_eq_one
  rw [← localCyclotomicCharacter_apply] at hspec
  set x := PadicInt.toZModPow 3 (localCyclotomicCharacter 2 K σ : ℤ_[2])
  have hcop : x.val.Coprime (2 ^ 3) := ZMod.val_coe_unit_coprime
    (Units.map (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)).toMonoidHom
      (localCyclotomicCharacter 2 K σ))
  have hlt : x.val < 8 := ZMod.val_lt x
  rw [map_add, map_pow, hspec, ← pow_mul] at hfix
  -- The exponents `5` and `7` send `ξ + ξ ^ 3` to its negative, which is impossible since it is
  -- a square root of `-2 ≠ 0`.
  have hne : ξ + ξ ^ 3 ≠ 0 := fun h ↦ by
    rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero] at ht2
    exact h2 ht2
  interval_cases hc : x.val
  · simp at hcop
  · exact .inl (by rw [← ZMod.natCast_zmod_val x, hc, Nat.cast_one])
  · norm_num at hcop
  · exact .inr (by rw [← ZMod.natCast_zmod_val x, hc, Nat.cast_ofNat])
  · norm_num at hcop
  · refine absurd ((mul_eq_zero.mp ?_).resolve_left h2) hne
    linear_combination (-1) * hfix + (ξ + ξ ^ 3 * (ξ ^ 8 - ξ ^ 4 + 1)) * h4
  · norm_num at hcop
  · refine absurd ((mul_eq_zero.mp ?_).resolve_left h2) hne
    linear_combination (-1) * hfix + (ξ ^ 3 + ξ * (ξ ^ 16 - ξ ^ 12 + ξ ^ 8 - ξ ^ 4 + 1)) * h4

end TauCeti
end
