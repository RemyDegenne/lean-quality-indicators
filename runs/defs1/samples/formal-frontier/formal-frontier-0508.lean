@[expose] public section

noncomputable section

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry.AffineRelationQuotient

universe u

variable {R X : AffineScheme.{u}} (s t : R ⟶ X)

/-- A map invariant under the pair `R ⇉ X` descends to the affine
coequalizer. -/
abbrev lift {Y : AffineScheme.{u}} (f : X ⟶ Y)
    (h : s ≫ f = t ≫ f) : quotient s t ⟶ Y :=
  coequalizer.desc f h

end AlgebraicGeometry.AffineRelationQuotient
end
end
