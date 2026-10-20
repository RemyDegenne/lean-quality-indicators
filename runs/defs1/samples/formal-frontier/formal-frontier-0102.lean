@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- Rotate an equator point through angle `π t` in its first two
coordinates, keeping the third coordinate fixed at zero. -/
def sphere2EquatorHalfTurnVector
    (t : unitInterval) (p : sphere2Equator) : E3 :=
  WithLp.toLp 2 ![
    Real.cos (Real.pi * (t : ℝ)) * (p.1.1 : E3) 0 -
      Real.sin (Real.pi * (t : ℝ)) * (p.1.1 : E3) 1,
    Real.sin (Real.pi * (t : ℝ)) * (p.1.1 : E3) 0 +
      Real.cos (Real.pi * (t : ℝ)) * (p.1.1 : E3) 1,
    0]

end SphereTopology
end
end
