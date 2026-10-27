public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {ι : Type*}

/-- The count vector cast into Euclidean space. -/
def multinomialToEuclidean (k : ι → ℕ) : EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm fun i => (k i : ℝ)

end Probability
end TauCeti
end
end
