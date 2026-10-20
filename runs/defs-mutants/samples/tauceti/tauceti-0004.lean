public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace

namespace TauCeti

variable {ι : Type*}

/-- The covariance matrix of a measure on a finite-dimensional Euclidean space. Its `(i, j)`
entry is the scalar covariance of the `i`th and `j`th coordinate projections. -/
def covMatrix (μ : Measure (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  fun i j => cov[fun z => z i, fun z => z i; μ]

end TauCeti
end
end
