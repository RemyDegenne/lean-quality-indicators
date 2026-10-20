@[expose] public section

noncomputable section MetricCodesNoncomputable

section

open scoped BigOperators InnerProductSpace

namespace MetricCodes

/-- The spherical code number used in the metric-code argument. -/
def sphericalCodeNumber (n : ℕ) (s : ℝ) : ℕ∞ :=
  ⨆ C : SphericalCode n s, (C.points.card : ℕ∞)

end MetricCodes
end
end MetricCodesNoncomputable
end
