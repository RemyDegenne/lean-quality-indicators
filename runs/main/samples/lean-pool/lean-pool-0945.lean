section

@[expose] public section

namespace NavierStokes.PulseEnergyHistory

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff

open OutgoingSchedule OutgoingTail UniformAngularReset OutgoingHistories

variable {d : TailData} {K : ℝ}

theorem normalized_history_bound {H g : ℝ → ℝ} {lam N C M y : ℝ}
    (hlam : 0 < lam) (hN : 0 < N) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hy : 0 ≤ y) (hy' : y ≤ 13 / lam)
    (hg : Continuous g) (hd : ∀ t ∈ Icc (0 : ℝ) y, HasDerivAt H (g t) t)
    (hsource : ∀ t ∈ Icc (0 : ℝ) y, |g t| ≤ N * M)
    (hinit : |H 0| ≤ N * C / lam) :
    |H y| / (N * Real.exp (-2 * lam * y)) ≤ (C + 13 * M) * Real.exp 26 / lam := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (uIcc_of_le hy ▸ ht)) (hg.intervalIntegrable 0 y)
  have hint : |∫ t in (0 : ℝ)..y, g t| ≤ N * M * y := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := y) (C := N * M) (f := g) (fun t ht => by
        rw [Real.norm_eq_abs]
        exact hsource t (uIcc_of_le hy ▸ uIoc_subset_uIcc ht))
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hy] using h
  have heq : H y = H 0 + ∫ t in (0 : ℝ)..y, g t := by linarith only [hi]
  have hvalue : |H y| ≤ N * (C + 13 * M) / lam := by
    calc
      _ ≤ |H 0| + |∫ t in (0 : ℝ)..y, g t| := by rw [heq]; exact abs_add_le _ _
      _ ≤ N * C / lam + N * M * y := add_le_add hinit hint
      _ ≤ N * C / lam + N * M * (13 / lam) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hy' (mul_nonneg hN.le hM)) _
      _ = _ := by ring
  have hfactor : 1 ≤ Real.exp 26 * Real.exp (-2 * lam * y) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    linarith only [hlam, hy', (le_div_iff₀ hlam).mp hy']
  apply (div_le_iff₀ (mul_pos hN (Real.exp_pos _))).mpr
  calc
    _ ≤ N * (C + 13 * M) / lam := hvalue
    _ ≤ (C + 13 * M) * Real.exp 26 / lam * (N * Real.exp (-2 * lam * y)) := by
      have h := mul_le_mul_of_nonneg_left hfactor
        (show 0 ≤ N * (C + 13 * M) / lam by positivity)
      convert! h using 1 <;> ring

end
end NavierStokes.PulseEnergyHistory
end
end
