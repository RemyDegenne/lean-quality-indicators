@[expose] public section

namespace CKN

theorem norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : Vec d → ℝ} (hu : MeasureTheory.IntegrableOn u U)
    (huDiff : ContDiff ℝ 1 u) (x : Vec d)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (hsegment :
      MeasureTheory.IntegrableOn
        (fun y => ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖)
        U) :
    ‖u x - integralAverage U u‖ ≤
      (MeasureTheory.volume U).toReal⁻¹ *
        ∫ y in U, ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume := by
  have hμinv_nonneg : 0 ≤ (MeasureTheory.volume U).toReal⁻¹ := by
    positivity
  have hconstInt : MeasureTheory.IntegrableOn (fun _ : Vec d => u x) U := by
    simp [MeasureTheory.IntegrableOn]
  have hsubInt : MeasureTheory.IntegrableOn (fun y => u x - u y) U := by
    simpa using! hconstInt.sub hu
  have hleftInt : MeasureTheory.IntegrableOn (fun y => ‖u x - u y‖) U := hsubInt.norm
  have hmono :
      (fun y => ‖u x - u y‖) ≤ᵐ[volumeMeasureOn U]
        (fun y => ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume) := by
    filter_upwards [] with y
    exact norm_sub_le_integral_norm_fderiv_mul_norm_sub_along_segment huDiff x y
  have hint :
      ∫ y in U, ‖u x - u y‖ ∂MeasureTheory.volume ≤
        ∫ y in U, ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (MeasureTheory.integral_mono_ae hleftInt hsegment hmono)
  calc
    ‖u x - integralAverage U u‖ ≤
        (MeasureTheory.volume U).toReal⁻¹ *
          ∫ y in U, ‖u x - u y‖ ∂MeasureTheory.volume :=
      norm_sub_integralAverage_le_volumeAverage_integral_norm_sub hu x hvol
    _ ≤ (MeasureTheory.volume U).toReal⁻¹ *
        ∫ y in U, ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
            exact mul_le_mul_of_nonneg_left hint hμinv_nonneg

end CKN
end
