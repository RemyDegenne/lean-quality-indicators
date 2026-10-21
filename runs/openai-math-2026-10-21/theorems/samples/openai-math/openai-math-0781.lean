namespace OAI

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter

open scoped Topology ContDiff

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_centered_square [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
  have hpoly (x : Ω) : (f x - ∫ y, f y ∂μ) ^ 2 =
      f x ^ 2 - (2 * ∫ y, f y ∂μ) * f x + (∫ y, f y ∂μ) ^ 2 := by ring
  have hadd := integral_add (hf2.sub (hf.const_mul (2 * ∫ y, f y ∂μ)))
    (integrable_const ((∫ y, f y ∂μ) ^ 2))
  have hsub := integral_sub hf2 (hf.const_mul (2 * ∫ y, f y ∂μ))
  simp only [Pi.sub_apply] at hadd hsub
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoly), hadd, hsub, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  ring

end
end PositiveEinsteinFour.Variance
end OAI
