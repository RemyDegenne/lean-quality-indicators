public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace Modulus

theorem wellFounded_dvd_and_ne : WellFounded fun 𝔪 𝔫 : Modulus K ↦ 𝔪 ∣ 𝔫 ∧ 𝔪 ≠ 𝔫 := by
  refine Subrelation.wf (fun {𝔪 𝔫} h ↦ ?_) (InvImage.wf
    (fun 𝔪 : Modulus K ↦ Ideal.absNorm 𝔪.finitePart + 𝔪.infinitePart.card) wellFounded_lt)
  obtain ⟨⟨⟨L, hL⟩, hinf⟩, hne⟩ := h
  have hnorm : Ideal.absNorm 𝔫.finitePart = Ideal.absNorm 𝔪.finitePart * Ideal.absNorm L := by
    rw [hL, map_mul]
  have h𝔫 : Ideal.absNorm 𝔫.finitePart ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr 𝔫.finitePart_ne_bot
  have hL0 : Ideal.absNorm L ≠ 0 := fun h0 ↦ h𝔫 (by rw [hnorm, h0, mul_zero])
  have h𝔪 : Ideal.absNorm 𝔪.finitePart ≠ 0 := fun h0 ↦ h𝔫 (by rw [hnorm, h0, zero_mul])
  have hcard := Finset.card_le_card hinf
  have hle : Ideal.absNorm 𝔪.finitePart ≤ Ideal.absNorm 𝔫.finitePart :=
    hnorm ▸ Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hL0)
  simp only [InvImage]
  by_contra hlt
  -- Both summands can only grow along divisibility, so if the sum does not grow, neither does.
  have hnorm_eq : Ideal.absNorm 𝔫.finitePart = Ideal.absNorm 𝔪.finitePart := by omega
  rw [hnorm] at hnorm_eq
  refine hne (Modulus.ext ?_ (Finset.eq_of_subset_of_card_le hinf (by omega)))
  rw [hL, Ideal.absNorm_eq_one_iff.mp ((Nat.mul_eq_left h𝔪).mp hnorm_eq), Ideal.mul_top]

end Modulus
end TauCeti.GlobalNumberFields
end
