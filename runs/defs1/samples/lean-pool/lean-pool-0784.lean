@[expose] public section

open MeasureTheory Metric Set

open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Local extension of a class.** `localExtFun` at the graph and the cutoff the chart
fixes, so the only argument left is the class. -/
def localExt (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hrc : r < c.radius)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  localExtFun c (chartGraph c x) (chartCutoff x hrc) u

end EllipticPdes.Extension
end
end
