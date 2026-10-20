public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti.Probability

variable {s ξ x : ℝ}

theorem integrable_generalizedParetoPDFReal (s ξ : ℝ) :
    Integrable (generalizedParetoPDFReal s ξ) := by
  rcases le_or_gt s 0 with hs | hs
  · have hzero : generalizedParetoPDFReal s ξ = 0 :=
      funext (generalizedParetoPDFReal_of_scale_nonpos hs ξ)
    rw [hzero]
    exact integrable_zero ℝ ℝ volume
  · apply Integrable.of_integral_ne_zero
    rw [integral_generalizedParetoPDFReal_eq_one hs ξ]
    exact one_ne_zero

end TauCeti.Probability
end
end
