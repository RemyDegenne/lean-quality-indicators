public noncomputable section

open MeasureTheory Metric Set Filter Topology

open scoped ENNReal

namespace TauCeti

section AddHaar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {f : E → ℝ≥0∞}

@[simp]
theorem eLpNorm_schwarzRearrangement (hf : AEMeasurable f μ) (p : ℝ≥0∞) :
    eLpNorm (schwarzRearrangement μ f) p μ = eLpNorm f p μ := by
  have hf' := hf.aestronglyMeasurable
  have hg : AEStronglyMeasurable (schwarzRearrangement μ f) μ :=
    (measurable_schwarzRearrangement μ f).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hg, eLpNorm_exponent_zero hf']
  rcases eq_or_ne p ∞ with rfl | hptop
  · rw [eLpNorm_exponent_top hg, eLpNorm_exponent_top hf']
    simp only [eLpNormEssSup_eq_essSup_enorm, enorm_eq_self, essSup_schwarzRearrangement]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hg,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf']
  simp only [enorm_eq_self]
  rw [lintegral_rpow_schwarzRearrangement μ hf (ENNReal.toReal_pos hp0 hptop)]

end AddHaar
end TauCeti
end
