@[expose] public section

noncomputable section

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry.AffineRelationQuotient

universe u

variable {R X : AffineScheme.{u}} (s t : R ⟶ X)

/-- The canonical map from `X` to the affine coequalizer. -/
abbrev quotientMap : X ⟶ quotient s t :=
  coequalizer.π s t

end AlgebraicGeometry.AffineRelationQuotient
end
end
