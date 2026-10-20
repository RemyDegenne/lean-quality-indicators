@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory UnitriangularStageCoordinateRing

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

/-- The stage's underlying over-scheme is affine space on its surviving entries.
This extends the full-group polynomial presentation in Milne, *Algebraic Groups*
(2017), item 2.9; it does not identify the stage as an additive group scheme. -/
def unitriangularStageUnderlyingAffineSpaceIso :
    unitriangularStageUnderlyingScheme K n r ≅
      (AffineSpace (SurvivingPair n r) (Spec (.of K))).asOver (Spec (.of K)) := by
  unfold unitriangularStageUnderlyingScheme Scheme.asOver OverClass.asOver
  refine Over.isoMk
    ((Scheme.Spec.mapIso (polynomialEquiv K n r).symm.toRingEquiv.toCommRingCatIso.op) ≪≫
      (AffineSpace.SpecIso (SurvivingPair n r) (.of K)).symm) ?_
  change (Scheme.Spec.mapIso
      (polynomialEquiv K n r).symm.toRingEquiv.toCommRingCatIso.op).hom ≫
      (AffineSpace.SpecIso (SurvivingPair n r) (.of K)).inv ≫
        (AffineSpace (SurvivingPair n r) (Spec (.of K)) ↘ Spec (.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (CoordinateRing K n r)))
  rw [AffineSpace.SpecIso_inv_over]
  change Spec.map (CommRingCat.ofHom (polynomialEquiv K n r).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (SurvivingPair n r) K))) =
    Spec.map (CommRingCat.ofHom (algebraMap K (CoordinateRing K n r)))
  rw [← Spec.map_comp]
  congr 1
  ext k
  exact (polynomialEquiv K n r).symm.commutes k

end AlgebraicGeometry
end
end
