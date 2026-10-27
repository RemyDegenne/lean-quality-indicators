public section

noncomputable section

open MeasureTheory ProbabilityTheory Ring

open scoped ENNReal MatrixOrder RealInnerProductSpace

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear part of displacement interpolation between two Gaussian covariances. -/
def gaussianInterpolationMatrix (S₁ S₂ : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  (1 - t) • 1 + t • geometricMean S₁⁻¹ʳ S₂

end TauCeti
end
end
