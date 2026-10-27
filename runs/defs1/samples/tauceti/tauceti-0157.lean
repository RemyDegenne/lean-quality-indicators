public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti.EuclideanHalfSpace

/-- The model half-space as a charted space over the product, with the collar identification as
its single chart.

Deliberately not an instance: `EuclideanHalfSpace (n + 1)` already carries the charted space
structure over itself, and a second one found by instance search would make every statement
about its charts ambiguous. Use it explicitly with `letI`. -/
@[instance_reducible]
noncomputable def collarModelChartedSpace (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
      (EuclideanHalfSpace (n + 1)) :=
  (collarDiffeomorph (k := ⊤) n).symm.toHomeomorph.toOpenPartialHomeomorph
    |>.singletonChartedSpace (by simp)

end TauCeti.EuclideanHalfSpace
end
end
