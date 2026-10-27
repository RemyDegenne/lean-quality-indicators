@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

section

open Filter Metric Topology

open scoped BigOperators InnerProductSpace Topology

namespace Hamming

/-- The top eigenvalue used in the binary-code argument. -/
def topEigenvalue (n k L : ℕ) : ℝ :=
  ⨆ x : {x : Space k L // x ≠ 0}, rayleigh n k L x

end Hamming
end
end MetricCodes
end MetricCodesNoncomputable
end
