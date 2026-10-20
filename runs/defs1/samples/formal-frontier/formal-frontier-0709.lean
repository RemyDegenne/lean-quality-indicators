@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- Bundle the radial interpolation as a jointly continuous map of time and
point. Time zero selects the component representative; time one returns the point. -/
def circlePunctureIntersectionRadialHomotopyMap :
    C(unitInterval × circlePunctureIntersection, circlePunctureIntersection) :=
  ⟨fun q => circlePunctureIntersectionRadialPoint q.1 q.2,
    continuous_circlePunctureIntersectionRadialPoint⟩

end SphereTopology
end
end
