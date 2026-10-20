public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {v : ℝ≥0} {x : ℝ}

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {m : ℝ}

theorem rnDeriv_logitNormalMeasure (m : ℝ) (hv : v ≠ 0) :
    (logitNormalMeasure m v).rnDeriv volume =ᵐ[volume] logitNormalPDF m v := by
  rw [logitNormalMeasure_eq_withDensity m hv]
  exact Measure.rnDeriv_withDensity volume (measurable_logitNormalPDF m v)

end TauCeti.Probability
end
end
