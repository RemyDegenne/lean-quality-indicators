/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularStagePolynomial
public import AlgebraicGroups.GroupScheme.UnitriangularStages
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Affine-space coordinates for the underlying unitriangular stage

The actual stage quotient represents affine space on the surviving strict-upper
entries, over the coefficient ring. This is an isomorphism of underlying schemes
over the base, not an isomorphism of group schemes with an additive group.

Milne's full-group polynomial presentation over a field is an antecedent;
the stage comparison is an isomorphism of underlying over-schemes.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.9 (the polynomial
  presentation of the full unitriangular algebraic group over a field).
* Mathlib contributors, `Mathlib.AlgebraicGeometry.AffineSpace`
  (`AffineSpace.SpecIso`).
* The earlier `UnitriangularGeometry` underlying-affine-space comparison
  supplies the `Spec`/`Over` proof pattern.
-/

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

/-- Each affine-space coordinate pulls back to the corresponding actual quotient entry. -/
theorem unitriangularStageUnderlyingAffineSpaceIso_preimage_variable
    (s : SurvivingPair n r) :
    Spec.preimage ((unitriangularStageUnderlyingAffineSpaceIso K n r).hom.left ≫
      (AffineSpace.SpecIso (SurvivingPair n r) (.of K)).hom) (MvPolynomial.X s) =
        quotient K n r (entry K n s.1.1.1 s.1.1.2) := by
  have hmap : (unitriangularStageUnderlyingAffineSpaceIso K n r).hom.left ≫
      (AffineSpace.SpecIso (SurvivingPair n r) (.of K)).hom =
        (Scheme.Spec.mapIso
          (polynomialEquiv K n r).symm.toRingEquiv.toCommRingCatIso.op).hom := by
    simp only [unitriangularStageUnderlyingAffineSpaceIso, id_eq, Over.isoMk_hom_left,
      Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hmap]
  change Spec.preimage
    (Spec.map (CommRingCat.ofHom (polynomialEquiv K n r).symm.toRingHom))
    (MvPolynomial.X s) = quotient K n r (entry K n s.1.1.1 s.1.1.2)
  rw [Spec.preimage_map]
  exact polynomialEquiv_symm_X K n r s

/-- Pullback in the reverse direction is the polynomial algebra equivalence. -/
theorem unitriangularStageUnderlyingAffineSpaceIso_preimage_inverse
    (f : CoordinateRing K n r) :
    Spec.preimage ((AffineSpace.SpecIso (SurvivingPair n r) (.of K)).inv ≫
      (unitriangularStageUnderlyingAffineSpaceIso K n r).inv.left) f =
        polynomialEquiv K n r f := by
  have hmap : (AffineSpace.SpecIso (SurvivingPair n r) (.of K)).inv ≫
      (unitriangularStageUnderlyingAffineSpaceIso K n r).inv.left =
        (Scheme.Spec.mapIso
          (polynomialEquiv K n r).symm.toRingEquiv.toCommRingCatIso.op).inv := by
    simp only [unitriangularStageUnderlyingAffineSpaceIso, id_eq, Over.isoMk_inv_left,
      Iso.trans_inv, Iso.symm_inv, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hmap]
  change Spec.preimage
    (Spec.map (CommRingCat.ofHom (polynomialEquiv K n r).toRingHom)) f =
      polynomialEquiv K n r f
  rw [Spec.preimage_map]
  rfl

end AlgebraicGeometry
