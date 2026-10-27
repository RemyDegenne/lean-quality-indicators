@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace EllipticPdes.Classical

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- The sum of the second coordinate partials. -/
def laplacianSum (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, partialD i (partialD i u) x

end EllipticPdes.Classical
end
end
