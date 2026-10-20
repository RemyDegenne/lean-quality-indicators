@[expose] public section

noncomputable section

namespace NavierStokes.StressActivation

open Set Filter MeasureTheory Metric

open ProfileHistories

open scoped Topology ContDiff

/-- Relative family, given by `relativeFactor T q.1.1 L (q.1.2, q.2)`. -/
noncomputable def relativeFamily (T : ℝ) (L : ProfileHistories.Field) (q : FamilyPoint) : ℝ :=
  relativeFactor T q.1.1 L (q.1.2, q.2)

end NavierStokes.StressActivation
end
end
