public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {μ : Measure ℝ≥0}

theorem integral_stieltjesInversion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ≥0 → E) :
    ∫ y, g y ∂stieltjesInversion μ = ∫ x, ((x : ℝ)⁻¹) • g x⁻¹ ∂μ := by
  rw [stieltjesInversion, Measure.inv, measurableEmbedding_inv.integral_map,
    integral_withDensity_eq_integral_smul (by fun_prop)]
  simp [NNReal.smul_def]

end MeasureTheory.Measure
end
end
