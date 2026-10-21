namespace OAI

section

section

open Set Filter MeasureTheory

open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma clippedCenter_logCoordinates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (lo hi : ℝ) (hle : lo ≤ hi)
    (hlo : lo ≤ Real.log (G T z).im) (hhi : Real.log z.im ≤ hi)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    clippedCenter lo hi hle (U u.toNNReal) (logLoewnerCoordinates G z u) =
      G u.toNNReal z - (U u.toNNReal : ℂ) := by
  obtain ⟨ha, hb⟩ := h.log_height_bounds T z hz u hu
  have hmem : Real.log (G u.toNNReal z).im ∈ Icc lo hi := ⟨hlo.trans ha, hb.trans hhi⟩
  have him := h.imag_positive _ z (h.live_at_real_time T z hz u hu.2)
  simp only [clippedCenter, clippedHeight, logLoewnerCoordinates, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    mul_one, zero_add, projIcc_of_mem hle hmem, Real.exp_log him]
  apply Complex.ext <;> simp

end SLEExactGauge
end
end
end OAI
