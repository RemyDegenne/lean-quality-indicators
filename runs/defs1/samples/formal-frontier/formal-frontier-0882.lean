public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The affine scheme represented by the dual symmetric algebra, over `Spec K`. -/
abbrev vectorGroupUnderlyingScheme : Over (Spec (.of K)) :=
  (Spec (.of (vectorGroupCoordinateRing K V))).asOver (Spec (.of K))

end AlgebraicGeometry
end
end
