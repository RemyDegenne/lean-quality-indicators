namespace OAI

noncomputable section

open scoped Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Real

namespace SKRatio.Scalar

lemma gSignFactor_denom (h : ℝ) : (2:ℝ) < (7/4)^2-m h^2 := by
  have hh := tanh_sq_lt_one h
  change m h^2 < 1 at hh
  linarith

end SKRatio.Scalar
end
end OAI
