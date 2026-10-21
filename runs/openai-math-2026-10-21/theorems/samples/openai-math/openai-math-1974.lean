namespace OAI

noncomputable section

open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric

open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

theorem potential_eq_source_green_integral
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (T : ℝ≥0) :
    potential κ θ b (κ*T) =
      ∫⁻ z in diskSourceCompact θ,
        ENNReal.ofReal (‖deriv (diskMap θ) z‖^dimension κ) *
          ENNReal.ofReal (greenDensity κ U γ G T z) := by
  have hK := diskSourceCompact_compact θ
  have hsub := diskSourceCompact_subset hθ
  have hd (z : ℂ) (hz : z ∈ diskSourceCompact θ) := diskMap_hasDerivAt hθ (hsub hz)
  rw [potential,← diskSourceCompact_image hθ,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK.measurableSet
      (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
      ((diskMap_injOn hθ).mono hsub)]
  apply setLIntegral_congr_fun hK.measurableSet
  intro z hz
  dsimp only
  rw [complex_derivative_real_det,abs_of_nonneg (sq_nonneg _),
    green_eq_transported_density κ hκ b U hUc γ G F hw hU θ (diskMap θ z) T,
    diskMapInv_diskMap hθ (hsub hz),
    ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _),← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [← (hd z hz).deriv,← Real.rpow_natCast,
    ← Real.rpow_add (diskMap_deriv_pos hθ (hsub hz))]
  congr 1
  simp only [codimension,dimension]
  ring

end SLEExactGauge.Target
end
end OAI
