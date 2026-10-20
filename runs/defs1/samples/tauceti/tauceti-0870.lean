public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal Real

namespace TauCeti

namespace Probability

variable {ν x : ℝ}

/-- The density of Student's t law with `ν` degrees of freedom, as a real-valued function.

For `ν ≤ 0` there is no such law and the density is `0`. -/
def studentTPDFReal (ν x : ℝ) : ℝ :=
  if 0 < ν then
    Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)) *
      (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))
  else 0

end Probability
end TauCeti
end
end
