@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- Before normalization, scale only the third coordinate by the homotopy
parameter.  The first two coordinates remain unchanged. -/
def sphere2PunctureIntersectionLinearVector
    (t : unitInterval) (p : sphere2PunctureIntersection) : E3 :=
  WithLp.toLp 2 ![(p.1.1 : E3) 0, (p.1.1 : E3) 1,
    (t : ℝ) * (p.1.1 : E3) 2]

end SphereTopology
end
end
