public section

namespace CFSG.CGT.Stroth77

section Fixed

variable {S : Type*} [Group S] [Finite S] {B : Subgroup S} {m : ℕ}

theorem fixed_rho_t_t220 {s : ℕ} {hs : 1 ≤ s} (D : StrothTypeData B (StrothTypeIndex.t220 s hs))
    {y : B} (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t220 s hs).action.φρ (D.ec y) = D.ec y := by
    have h := D.ρ_conj y
    change D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t220 s hs).action.φρ (D.ec y) at h
    rw [← h, hρ]
  have ht' : (StrothTypeIndex.t220 s hs).action.φt (D.ec y) = D.ec y := by
    have h := D.t_conj y
    change D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t220 s hs).action.φt (D.ec y) at h
    rw [← h, ht]
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens _ (D.ec y)
  rw [hy, rho_apply_gens_t220] at hρ'
  rw [hy, t_apply_gens_t220] at ht'
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hρ'
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq ht'
  change (2 : ℤ) ^ (s + 4) ∣ _ at hρ1 hρ2 ht1
  have h3 : IsCoprime ((2 : ℤ) ^ (s + 4)) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  have hl : (2 : ℤ) ^ (s + 4) ∣ l := by
    refine h3.dvd_of_dvd_mul_left ?_
    have := dvd_add hρ1 hρ2
    convert this using 1
    ring
  have hj : (2 : ℤ) ^ (s + 4) ∣ j := by
    have := dvd_sub hρ1 hl
    convert this using 1
    ring
  have h4i : (2 : ℤ) ^ (s + 4) ∣ 4 * i := by
    have := dvd_sub (dvd_add (dvd_mul_of_dvd_right hj (1 + 7 * Type120.iV (s + 4)))
      (dvd_mul_of_dvd_right hl (2 * Type120.iV (s + 4)))) ht1
    convert this using 1
    ring
  have hi : (2 : ℤ) ^ (s + 2) ∣ i := by
    have h16 : (2 : ℤ) ^ (s + 4) = 4 * 2 ^ (s + 2) := by ring
    rw [h16] at h4i
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4i
  apply D.ec_eq_zero_iff.mp
  rw [hy]
  have h0 := zsmul_gens_eq_of_dvd (k := (StrothTypeIndex.t220 s hs).k) (p := i) (q := j) (r := l)
    (p' := 0) (q' := 0) (r' := 0)
    (by change (2 : ℤ) ^ (s + 2) ∣ 0 - i; rw [zero_sub, dvd_neg]; exact hi)
    (by change (2 : ℤ) ^ (s + 4) ∣ 0 - j; rw [zero_sub, dvd_neg]; exact hj)
    (by change (2 : ℤ) ^ (s + 4) ∣ 0 - l; rw [zero_sub, dvd_neg]; exact hl)
  rw [h0]
  simp

end Fixed
end CFSG.CGT.Stroth77
end
