@[expose] public section

open MeasureTheory Metric Filter Topology Set

open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

theorem stepProfile_eq_one {t : ℝ} (ht : 2 ≤ t) : stepProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

end EllipticPdes.Extension
end
end
