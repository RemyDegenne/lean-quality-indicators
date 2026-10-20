public section

noncomputable section

namespace TauCeti.Yamabe

open MeasureTheory Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_sphereYamabeConstant
    (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ (bubble t b) x‖ ^ 2 =
      sphereYamabeConstant (finrank ℝ E) *
        (∫ x, bubble t b x ^ criticalExponent (finrank ℝ E)) ^
          (2 / criticalExponent (finrank ℝ E)) := by
  have hp : 2 / criticalExponent (finrank ℝ E) = ((finrank ℝ E : ℝ) - 2) / finrank ℝ E := by
    have hn₀ : finrank ℝ E ≠ 0 := by omega
    have h₀ : (finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast hn₀
    have h₂ : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn.ne')
    rw [criticalExponent_def]
    field_simp
  rw [conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_roundSphereVolume hn ht b,
    integral_bubble_rpow_criticalExponent_eq_roundSphereVolume (by omega) hn.ne' ht b, hp,
    sphereYamabeConstant_mul_roundSphereVolume_rpow (by omega)]

end TauCeti.Yamabe
end
end
