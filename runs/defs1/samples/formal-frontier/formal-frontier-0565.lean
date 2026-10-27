@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

/-- The affine scheme over `Spec K` represented by the Hopf quotient. -/
abbrev unitriangularGroupUnderlyingScheme : Over (Spec (.of K)) :=
  (Spec (.of (UnitriangularCoordinateRing.CoordinateRing K n))).asOver (Spec (.of K))

end AlgebraicGeometry
end
end
