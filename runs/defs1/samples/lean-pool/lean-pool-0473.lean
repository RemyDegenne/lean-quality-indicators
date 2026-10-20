@[expose] public section

open Function Filter Set Metric

open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-- Devaney chaos on the plane: continuity, dense periodic points, and transitivity. -/
def IsDevaneyChaotic (f : ℂ → ℂ) : Prop :=
  Continuous f ∧ Dense (Function.periodicPts f) ∧
    MulAction.IsTopologicallyTransitive (IterateMulAct f) ℂ

end
end ExponentialJuliaSetMisiurewicz
end
