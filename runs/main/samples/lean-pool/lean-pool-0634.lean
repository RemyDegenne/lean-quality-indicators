public section

open MeasureTheory Filter

open CKN.Foundation.Parabolic

open scoped ENNReal

namespace CKN.Leray

theorem l2_distance_le_of_lintegral_sq_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f g : α → E} {δ : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hδ : 0 ≤ δ)
    (herror : ∫⁻ x, ‖f x - g x‖ₑ ^ (2 : ℝ) ∂μ ≤
      ENNReal.ofReal δ ^ (2 : ℕ)) :
    dist (hf.toLp f) (hg.toLp g) ≤ δ:= by
  have hfg : MemLp (f - g) 2 μ := hf.sub hg
  have hLpEq : hf.toLp f - hg.toLp g = hfg.toLp (f - g) :=
    (hf.toLp_sub hg).symm
  have hnormSq : ‖hfg.toLp (f - g)‖ ^ 2 =
      (∫⁻ x, ‖f x - g x‖ₑ ^ (2 : ℝ) ∂μ).toReal := by
    rw [Lp.norm_toLp]
    calc
      (eLpNorm (f - g) 2 μ).toReal ^ 2 =
          (eLpNorm (f - g) 2 μ).toReal ^ (2 : ℝ) := by
        exact (Real.rpow_natCast _ _).symm
      _ = (eLpNorm (f - g) 2 μ ^ (2 : ℝ)).toReal := by
        exact ENNReal.toReal_rpow _ _
      _ = (∫⁻ x, ‖f x - g x‖ₑ ^ (2 : ℝ) ∂μ).toReal := by
        rw [eLpNorm_two_rpow_eq_lintegral hfg.aestronglyMeasurable]
        simp only [Pi.sub_apply]
  have hreal :
      (∫⁻ x, ‖f x - g x‖ₑ ^ (2 : ℝ) ∂μ).toReal ≤ δ ^ 2 := by
    calc
      (∫⁻ x, ‖f x - g x‖ₑ ^ (2 : ℝ) ∂μ).toReal ≤
          (ENNReal.ofReal δ ^ (2 : ℕ)).toReal :=
        ENNReal.toReal_mono (by simp) herror
      _ = δ ^ 2 := by simp [ENNReal.toReal_pow, hδ]
  rw [dist_eq_norm_sub, hLpEq]
  nlinarith only [hnormSq, hreal, norm_nonneg (hfg.toLp (f - g)), hδ]

end CKN.Leray
end
