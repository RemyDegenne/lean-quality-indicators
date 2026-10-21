namespace OAI

section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

open Matrix

open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma stablePoissonTotal_pos {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b), 0 < stablePoissonTotal η := by
  filter_upwards [stablePoisson_total_positive hb0,stablePoisson_total_finite hb0 hb1] with η hp hf
  exact ENNReal.toReal_pos hp.ne' hf

end SphericalPerceptron
end
end
end OAI
