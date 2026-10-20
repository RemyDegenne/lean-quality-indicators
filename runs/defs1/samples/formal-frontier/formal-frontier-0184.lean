@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory UnitriangularStageCoordinateRing

open scoped Classical

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

/-- The complete algebra pullback of the affine coordinate projection, using
Mathlib's `MvPolynomial.rename` and the stage polynomial equivalence. -/
def stageProductCoordinatePullback (hr : 1 ≤ r) :
    MvPolynomial (Matrix.UnitriangularGroup.superdiagonalIndex n r) K →ₐ[K]
      CoordinateRing K n r :=
  (polynomialEquiv K n r).symm.toAlgHom.comp
    (MvPolynomial.rename (stageSuperdiagonalInclusion n r hr))

end AlgebraicGeometry
end
end
