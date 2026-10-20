section

section

section

@[expose] public section

noncomputable section

open Filter

namespace NavierStokesR3.ComparisonYoung

theorem cutoff_expression_le {C A R : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hR : 1 ≤ R) :
    C * ((A + R⁻¹) ^ (1 / 2 : ℝ) + 1) *
        (R⁻¹ * A + R ^ (-2 : ℝ)) +
      C * R ^ (-7 / 4 : ℝ) * (A + R⁻¹) ^ (3 / 4 : ℝ) +
      C * R⁻¹ * (A + R⁻¹) ^ (3 / 2 : ℝ) ≤
        4 * C / R * (A + 1) ^ (3 / 2 : ℝ) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hInv : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  have hInv1 : R⁻¹ ≤ 1 := (inv_le_one₀ hRpos).mpr hR
  have hx : 0 ≤ A + R⁻¹ := add_nonneg hA hInv
  have hxB : A + R⁻¹ ≤ A + 1 := add_le_add_right hInv1 A
  have hB1 : 1 ≤ A + 1 := le_add_of_nonneg_left hA
  have hBpos : 0 < A + 1 := add_pos_of_nonneg_of_pos hA zero_lt_one
  have hR2 : R ^ (-2 : ℝ) ≤ R⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (-2 : ℝ) ≤ -1))
  have hR74 : R ^ (-7 / 4 : ℝ) ≤ R⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (-7 / 4 : ℝ) ≤ -1))
  have hhalf : (A + R⁻¹) ^ (1 / 2 : ℝ) + 1 ≤
      2 * (A + 1) ^ (1 / 2 : ℝ) := by
    have hmon := Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hone := Real.one_le_rpow hB1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact (add_le_add hmon hone).trans_eq (two_mul _).symm
  have hlinear : R⁻¹ * A + R ^ (-2 : ℝ) ≤ R⁻¹ * (A + 1) := by
    rw [mul_add, mul_one]
    exact add_le_add_right hR2 _
  have hlinear0 : 0 ≤ R⁻¹ * A + R ^ (-2 : ℝ) :=
    add_nonneg (mul_nonneg hInv hA) (Real.rpow_nonneg hRpos.le _)
  have hprod : (A + 1) ^ (1 / 2 : ℝ) * (A + 1) =
      (A + 1) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hBpos.ne']
    norm_num
  have hfactor : ((A + R⁻¹) ^ (1 / 2 : ℝ) + 1) *
      (R⁻¹ * A + R ^ (-2 : ℝ)) ≤ 2 * R⁻¹ * (A + 1) ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ (2 * (A + 1) ^ (1 / 2 : ℝ)) * (R⁻¹ * (A + 1)) :=
        mul_le_mul hhalf hlinear hlinear0
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hBpos.le _))
      _ = 2 * R⁻¹ * ((A + 1) ^ (1 / 2 : ℝ) * (A + 1)) := by ring
      _ = _ := by rw [hprod]
  have hthreeQuarters : (A + R⁻¹) ^ (3 / 4 : ℝ) ≤
      (A + 1) ^ (3 / 2 : ℝ) :=
    (Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 3 / 4)).trans
      (Real.rpow_le_rpow_of_exponent_le hB1
        (by norm_num : (3 / 4 : ℝ) ≤ 3 / 2))
  have hthreeHalves : (A + R⁻¹) ^ (3 / 2 : ℝ) ≤
      (A + 1) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hterm1 := mul_le_mul_of_nonneg_left hfactor hC
  have hterm2 := mul_le_mul_of_nonneg_left
    (mul_le_mul hR74 hthreeQuarters (Real.rpow_nonneg hx _) hInv) hC
  have hterm3 := mul_le_mul_of_nonneg_left hthreeHalves (mul_nonneg hC hInv)
  rw [mul_assoc C, mul_assoc C (R ^ (-7 / 4 : ℝ))]
  exact (add_le_add (add_le_add hterm1 hterm2) hterm3).trans_eq (by ring)

end NavierStokesR3.ComparisonYoung
end
end
end
end
end
