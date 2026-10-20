@[expose] public section

namespace FD1D

noncomputable section

open Set MeasureTheory ProbabilityTheory

open scoped ENNReal ProbabilityTheory

namespace V5.ContinuousProcess

variable {L m : ℕ}

/-- One-period trajectory cost from a fixed spatial state. -/
def trajectoryExpectedSquaredCostFromState
    (s₀ : SpatialState m) (a : ℝ) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) : ℝ :=
  trajectoryExpectedSquaredCostFrom
    (L := L) (Measure.dirac s₀) a hm fallback t

end V5.ContinuousProcess
end
end FD1D
end
