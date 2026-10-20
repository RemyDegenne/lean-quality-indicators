@[expose] public section

namespace NavierStokes.PhaseEstimates

open Set Filter

open scoped Topology InnerProductSpace

theorem velocity_error_scaled {M S ε k : ℝ}
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hk : 0 < k) (hε : 0 ≤ ε) :
    M ^ 3 / S + (M * (1 / k) + 2 * M * (M * (1 / S ^ 3 + ε ^ 2))) +
      |ε| * (3 * M ^ 2) ≤ phaseConstant M * phaseError S ε k := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hE : 0 ≤ phaseError S ε k := by unfold phaseError; positivity
  have hS1 : 0 ≤ 1 / S := one_div_nonneg.mpr hS0.le
  have hS2 : 0 ≤ S * ε ^ 2 := mul_nonneg hS0.le (sq_nonneg ε)
  have hS3 : 0 ≤ S / k := div_nonneg hS0.le hk.le
  have hS4 : 0 ≤ ε * S := mul_nonneg hε hS0.le
  have h0 : 1 / S ≤ phaseError S ε k := by
    unfold phaseError
    exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg (le_add_of_nonneg_right hS2) hS3) hS4
  have h1 : 1 / S + S * ε ^ 2 ≤ phaseError S ε k := by
    unfold phaseError
    exact le_add_of_le_of_nonneg (le_add_of_nonneg_right hS3) hS4
  have h2 : S / k ≤ phaseError S ε k := by
    unfold phaseError
    exact le_add_of_le_of_nonneg (le_add_of_nonneg_left (add_nonneg hS1 hS2)) hS4
  have h3 : ε * S ≤ phaseError S ε k := by
    unfold phaseError
    exact le_add_of_nonneg_left (add_nonneg (add_nonneg hS1 hS2) hS3)
  have ha : M ^ 3 / S ≤ M ^ 3 * phaseError S ε k := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h0 (pow_nonneg hM0 3)
  have hb : M * (1 / k) ≤ M * phaseError S ε k :=
    mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right hS hk.le).trans h2) hM0
  have hc : 2 * M * (M * (1 / S ^ 3 + ε ^ 2)) ≤ 2 * M ^ 2 * phaseError S ε k := by
    have hh : 1 / S ^ 3 + ε ^ 2 ≤ phaseError S ε k :=
      (add_le_add (inverse_cube_bounds hS).1
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hS (sq_nonneg ε))).trans h1
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * M ^ 2 by positivity)
    exact (by ring : 2 * M * (M * (1 / S ^ 3 + ε ^ 2)) = 2 * M ^ 2 * (1 / S ^ 3 + ε ^ 2)).trans_le
      hh'
  have hd : |ε| * (3 * M ^ 2) ≤ 3 * M ^ 2 * phaseError S ε k := by
    rw [abs_of_nonneg hε]
    have hεle : ε ≤ ε * S := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hS hε
    have hh : ε ≤ phaseError S ε k := hεle.trans h3
    linarith only [mul_le_mul_of_nonneg_left hh (show 0 ≤ 3 * M ^ 2 by positivity)]
  have hm2 : M ≤ M ^ 2 := by nlinarith only [hM]
  have hm3 : M ^ 2 ≤ M ^ 3 := by
    linarith only [mul_le_mul_of_nonneg_left hM (sq_nonneg M)]
  have hm4 : 0 ≤ M ^ 4 := pow_nonneg hM0 _
  have hcoeff : M ^ 3 + M + 5 * M ^ 2 ≤ phaseConstant M := by
    unfold phaseConstant
    linarith only [hm2, hm3, hm4, pow_nonneg hM0 3]
  calc
    _ ≤ M ^ 3 * phaseError S ε k + (M * phaseError S ε k + 2 * M ^ 2 * phaseError S ε k) +
        3 * M ^ 2 * phaseError S ε k := add_le_add (add_le_add ha (add_le_add hb hc)) hd
    _ = (M ^ 3 + M + 5 * M ^ 2) * phaseError S ε k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hE

end NavierStokes.PhaseEstimates
end
