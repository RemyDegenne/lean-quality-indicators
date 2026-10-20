@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The group object represented by the determinant-localized Hopf algebra. -/
abbrev generalLinearGroupScheme : Grp (Over (Spec (.of K))) :=
  ⟨generalLinearGroupUnderlyingScheme K n⟩

end AlgebraicGeometry
end
end
