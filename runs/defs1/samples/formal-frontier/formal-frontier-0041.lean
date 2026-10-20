@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory UnitriangularStageCoordinateRing

open scoped Classical

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

/-- Kill the higher-gap variables and retain the current superdiagonal,
using Mathlib's `MvPolynomial.killCompl`. -/
def stageProductCoordinateKill (hr : 1 ≤ r) :
    MvPolynomial (SurvivingPair n r) K →ₐ[K]
      MvPolynomial (Matrix.UnitriangularGroup.superdiagonalIndex n r) K :=
  MvPolynomial.killCompl (stageSuperdiagonalInclusion_injective n r hr)

end AlgebraicGeometry
end
end
