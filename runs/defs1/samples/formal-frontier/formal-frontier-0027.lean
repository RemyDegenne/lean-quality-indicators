@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- Insert a circle point into the first two coordinates of `E3`; the third
coordinate is zero. -/
def sphere1ToSphere2EquatorVector (p : Metric.sphere (0 : E2) 1) : E3 :=
  WithLp.toLp 2 ![(p.1 : E2) 0, (p.1 : E2) 1, 0]

end SphereTopology
end
end
