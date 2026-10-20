@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The south pole `(0, -1)`, defined as the antipode of `northPoint`. -/
def southPoint : Metric.sphere (0 : E2) 1 := -northPoint

end SphereTopology
end
end
