@[expose] public section

noncomputable section

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry.AffineRelationQuotient

universe u

variable {R X : AffineScheme.{u}} (s t : R ⟶ X)

/-- The affine coequalizer is canonically the spectrum of the invariant
ring. -/
def quotientInvariantSpecIso :
    (quotient s t).obj ≅ Spec (CommRingCat.of (coordinateInvariantRing s t)) :=
  (quotient s t).obj.isoSpec ≪≫
    Scheme.Spec.mapIso (quotientInvariantIso s t).symm.op

end AlgebraicGeometry.AffineRelationQuotient
end
end
