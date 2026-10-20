@[expose] public section

open MeasureTheory Metric Filter Topology Set

open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

theorem stepProfile_le_one (t : ℝ) : stepProfile t ≤ 1 := Real.smoothTransition.le_one _

end EllipticPdes.Extension
end
end
