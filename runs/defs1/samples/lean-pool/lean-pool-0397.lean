@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

section

open scoped BigOperators Matrix

namespace Boolean

variable {n : ℕ}

/-- The euclidean layer used in the binary-code argument. -/
abbrev EuclideanLayer (n k : ℕ) := EuclideanSpace ℝ (Level n k)

end Boolean
end
end MetricCodes
end MetricCodesNoncomputable
end
