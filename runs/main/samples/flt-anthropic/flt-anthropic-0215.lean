namespace P2MW.S_rademacher_phi_level_congruence

set_option autoImplicit false

namespace DedekindSumRows

theorem etaPhase_witness_five (j : ℕ) :
    12 * ((((4 * j + 2 : ℕ) + 3 : ℤ) : ℚ) * (1 - ((12 * j + 5 : ℕ) : ℚ))
          / (12 * ((12 * j + 5 : ℕ) : ℚ))
        + dedekindSum 3 1 - dedekindSum 3 (12 * j + 5))
      = ((Nat.gcd ((12 * j + 5) - 1) 12 : ℕ) : ℚ) * (-(2 * (j : ℤ) + 1)) ∧
    Nat.Coprime (Int.natAbs (-(2 * (j : ℤ) + 1)))
      (((12 * j + 5) - 1) / Nat.gcd ((12 * j + 5) - 1) 12) := by
  have hgcd : Nat.gcd ((12 * j + 5) - 1) 12 = 4 := by
    rw [show (12 * j + 5) - 1 = 4 + j * 12 from by omega, Nat.gcd_add_mul_right_left]
    decide
  have hL : ((12 * j + 5 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  constructor
  · have hco : Nat.Coprime 3 (12 * j + 5) := by
      rw [Nat.coprime_comm]
      unfold Nat.Coprime
      rw [show 12 * j + 5 = 2 + (4 * j + 1) * 3 from by ring, Nat.gcd_add_mul_right_left]
      decide
    have hrec := dedekindSum_add_dedekindSum 3 (12 * j + 5) (by norm_num) (by omega) hco
    have hs23 : dedekindSum 2 3 = -(1 / 18 : ℚ) := by
      rw [show (2 : ℤ) = -1 + 1 * ((3 : ℕ) : ℤ) from by norm_num, dedekindSum_add_mul,
        show (-1 : ℤ) = -(1 : ℤ) from rfl, dedekindSum_neg, dedekindSum_one_left]
      norm_num
    have hl3 : dedekindSum ((12 * j + 5 : ℕ) : ℤ) 3 = dedekindSum 2 3 := by
      rw [show ((12 * j + 5 : ℕ) : ℤ) = 2 + ((4 * j + 1 : ℕ) : ℤ) * ((3 : ℕ) : ℤ) from by
        push_cast; ring, dedekindSum_add_mul]
    have hs3l : dedekindSum 3 (12 * j + 5)
        = ((3 : ℚ) / (12 * j + 5 : ℕ) + ((12 * j + 5 : ℕ) : ℚ) / 3
            + 1 / (3 * ((12 * j + 5 : ℕ) : ℚ))) / 12 - 1 / 4 + 1 / 18 := by
      have h := hrec
      rw [hl3, hs23] at h
      linarith [h]
    rw [hgcd, dedekindSum_one_right, hs3l]
    push_cast
    field_simp
    ring
  ·
    rw [hgcd, show ((12 * j + 5) - 1) / 4 = 3 * j + 1 from by omega,
      show (-(2 * (j : ℤ) + 1)) = -((2 * j + 1 : ℕ) : ℤ) from by push_cast; ring,
      Int.natAbs_neg, Int.natAbs_natCast]
    have ha := Nat.gcd_dvd_left (2 * j + 1) (3 * j + 1)
    have hb := Nat.gcd_dvd_right (2 * j + 1) (3 * j + 1)
    have h1 : Nat.gcd (2 * j + 1) (3 * j + 1) ∣ 1 := by
      have h3 := Nat.dvd_sub (Dvd.dvd.mul_left ha 3) (Dvd.dvd.mul_left hb 2)
      rwa [show 3 * (2 * j + 1) - 2 * (3 * j + 1) = 1 from by omega] at h3
    exact Nat.dvd_one.mp h1

end DedekindSumRows
end P2MW.S_rademacher_phi_level_congruence
