/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AdditiveProductAffineSpace
public import AlgebraicGroups.GroupScheme.UnitriangularStageAffineSpace
public import AlgebraicGroups.GroupScheme.UnitriangularStageCoordinates
public import AlgebraicGroups.Algebra.UnitriangularStageKernel
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Positive-stage coordinates and the underlying affine projection

Under the coordinate identifications, the positive-stage group-scheme coordinate
map, after forgetting the group structure, becomes the scheme projection from
affine space on all surviving entries onto the current-superdiagonal coordinates. Its coordinate-ring
pullback goes in the opposite direction, from polynomials in the current
coordinates into the stage coordinate ring. This identifies the entire arrow
over the base, not just its points. Sending higher variables to zero defines
the ring pullback of a section of this underlying over-scheme projection;
the section does not assert compatibility with group multiplication.

Milne's unitriangular examples and filtration motivate the setting but do not
state this arbitrary-ring positive-stage over-scheme projection or section.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.9 and item 6.49
  (unitriangular groups and their filtration); item 2.1 (the additive group).
* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename` (variable renaming and
  `MvPolynomial.killCompl`), `Mathlib.AlgebraicGeometry.AffineSpace`
  (`AffineSpace.SpecIso`), and the categorical products and affine-Spec/global-
  section constructions cited in `AdditiveProductAffineSpace`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory UnitriangularStageCoordinateRing
open scoped Classical

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

/-- An index on the current superdiagonal is the same matrix position among
the entries surviving the `r`-th stage ideal. -/
def stageSuperdiagonalInclusion (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) : SurvivingPair n r := by
  let pair : UnitriangularCoordinateRing.StrictUpperPair (Fin n) :=
    ⟨ij.1, Fin.lt_def.mpr (by have hgap := ij.2; omega)⟩
  refine ⟨pair, ?_⟩
  change ij.1.1.val + r ≤ ij.1.2.val
  exact le_of_eq ij.2.symm

theorem stageSuperdiagonalInclusion_injective (hr : 1 ≤ r) :
    Function.Injective (stageSuperdiagonalInclusion n r hr) := by
  intro ij kl heq
  apply Subtype.ext
  change ij.1 = kl.1
  exact congrArg (fun s : SurvivingPair n r => s.1.1) heq

/-- The image consists of the surviving entries of gap *exactly* `r`. -/
theorem mem_range_stageSuperdiagonalInclusion (hr : 1 ≤ r)
    (s : SurvivingPair n r) :
    s ∈ Set.range (stageSuperdiagonalInclusion n r hr) ↔
      s.1.1.2.val = s.1.1.1.val + r := by
  constructor
  · rintro ⟨ij, hs⟩
    rw [← hs]
    exact ij.2
  · intro hgap
    refine ⟨⟨s.1.1, hgap⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- A surviving position not on the present superdiagonal has larger gap. -/
theorem stageSurviving_gap_gt_of_not_mem_range (hr : 1 ≤ r)
    (s : SurvivingPair n r)
    (hs : s ∉ Set.range (stageSuperdiagonalInclusion n r hr)) :
    s.1.1.1.val + r < s.1.1.2.val := by
  have hneq : s.1.1.2.val ≠ s.1.1.1.val + r :=
    fun h => hs ((mem_range_stageSuperdiagonalInclusion n r hr s).2 h)
  have hle := s.2
  omega

/-- The complete algebra pullback of the affine coordinate projection, using
Mathlib's `MvPolynomial.rename` and the stage polynomial equivalence. -/
def stageProductCoordinatePullback (hr : 1 ≤ r) :
    MvPolynomial (Matrix.UnitriangularGroup.superdiagonalIndex n r) K →ₐ[K]
      CoordinateRing K n r :=
  (polynomialEquiv K n r).symm.toAlgHom.comp
    (MvPolynomial.rename (stageSuperdiagonalInclusion n r hr))

@[simp] theorem stageProductCoordinatePullback_X (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    stageProductCoordinatePullback K n r hr (MvPolynomial.X ij) =
      coordinate K n r ij := by
  change (polynomialEquiv K n r).symm
      (MvPolynomial.rename (stageSuperdiagonalInclusion n r hr)
        (MvPolynomial.X ij)) = _
  rw [MvPolynomial.rename_X, polynomialEquiv_symm_X]
  rfl

/-- The official positive-stage coordinate algebra map is the corresponding
polynomial projection, on its *entire* rank-one coordinate algebra. -/
theorem stageCoordinateAlgHom_eq_productPullback (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    coordinateAlgHom K n r ij =
      (stageProductCoordinatePullback K n r hr).comp
        (additiveProductCoordinateAlgHom K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r) ij) := by
  let : AddCommMonoid (CoordinateRing K n r) :=
    (inferInstance : CommRing (CoordinateRing K n r)).toCommSemiring.toAddCommMonoid
  let : Module K (CoordinateRing K n r) := Algebra.toModule
  apply SymmetricAlgebra.algHom_ext (R := K) (M := K)
    (A := CoordinateRing K n r)
  ext
  change coordinateAlgHom K n r ij (additiveGroupCoordinate K) =
    stageProductCoordinatePullback K n r hr
      (additiveProductCoordinateAlgHom K
        (Matrix.UnitriangularGroup.superdiagonalIndex n r) ij
          (additiveGroupCoordinate K))
  rw [coordinateAlgHom_coordinate, additiveProductCoordinateAlgHom_coordinate,
    stageProductCoordinatePullback_X]

/-- The official stage affine-space iso, composed with the generic polynomial
spectrum/affine-space iso in the reverse direction. -/
def unitriangularStageUnderlyingSpecIso :
    unitriangularStageUnderlyingScheme K n r ≅
      additiveGroupAffineProductScheme K (SurvivingPair n r) :=
  unitriangularStageUnderlyingAffineSpaceIso K n r ≪≫
    (additiveGroupAffineProductSpecToSpaceIso K (SurvivingPair n r)).symm

/-- The left component of this over-isomorphism is the official polynomial
algebra equivalence, in the contravariant direction. -/
theorem unitriangularStageUnderlyingSpecIso_hom_left :
    (unitriangularStageUnderlyingSpecIso K n r).hom.left =
      Spec.map (CommRingCat.ofHom (polynomialEquiv K n r).symm.toRingHom) := by
  change (unitriangularStageUnderlyingAffineSpaceIso K n r).hom.left ≫
    (AffineSpace.SpecIso (SurvivingPair n r) (.of K)).hom = _
  simp only [unitriangularStageUnderlyingAffineSpaceIso, id_eq, Over.isoMk_hom_left,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Contravariant spectrum map of the inclusion of current-stage variables. -/
def stageProductSpecRename (hr : 1 ≤ r) :
    additiveGroupAffineProductScheme K (SurvivingPair n r) ⟶
      additiveGroupAffineProductScheme K
        (Matrix.UnitriangularGroup.superdiagonalIndex n r) :=
  (algSpec (.of K)).map
    (CommAlgCat.ofHom (MvPolynomial.rename
      (stageSuperdiagonalInclusion n r hr) :
        MvPolynomial (Matrix.UnitriangularGroup.superdiagonalIndex n r) K →ₐ[K]
          MvPolynomial (SurvivingPair n r) K)).op

/-- The actual coordinate projection agrees with the polynomial projection
after composing with the genuine product projection at any index. -/
theorem unitriangularStage_projection_triangle (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    ((unitriangularStageCoordinateMap K n r hr).hom.hom ≫
        (additiveGroupProductUnderlyingSpecIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom) ≫
          additiveGroupAffineProductProjection K
            (Matrix.UnitriangularGroup.superdiagonalIndex n r) ij =
      ((unitriangularStageUnderlyingSpecIso K n r).hom ≫
        stageProductSpecRename K n r hr) ≫
          additiveGroupAffineProductProjection K
            (Matrix.UnitriangularGroup.superdiagonalIndex n r) ij := by
  rw [Category.assoc, additiveGroupProductUnderlyingSpecIso_hom_projection]
  have hproj := congrArg (fun f : unitriangularStageScheme K n r ⟶
      additiveGroupScheme K => f.hom.hom)
    (unitriangularStageCoordinateMap_π K n r hr ij)
  change (unitriangularStageCoordinateMap K n r hr).hom.hom ≫
      (Limits.Pi.π (fun _ : Matrix.UnitriangularGroup.superdiagonalIndex n r =>
        additiveGroupScheme K) ij).hom.hom =
        (unitriangularStageCoordinateProjection K n r hr ij).hom.hom at hproj
  rw [hproj]
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left,
    unitriangularStageCoordinateProjection_left,
    unitriangularStageUnderlyingSpecIso_hom_left]
  change _ = _ ≫
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.rename (stageSuperdiagonalInclusion n r hr)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (additiveProductCoordinateAlgHom K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r) ij).toRingHom)
  rw [← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rw [coordinateBialgHom_toAlgHom,
    stageCoordinateAlgHom_eq_productPullback]
  rfl

/-- Equality of the *entire* underlying over-arrows, by the generic
polynomial product fan's universal property for arbitrary over-schemes.
This uses Mathlib's `MvPolynomial.rename` and the affine-Spec/product
constructions cited above; Milne's item 6.49 is filtration context, not a
statement of this over-scheme arrow identity. -/
theorem unitriangularStageCoordinateMap_underlying_spec (hr : 1 ≤ r) :
    (unitriangularStageCoordinateMap K n r hr).hom.hom ≫
        (additiveGroupProductUnderlyingSpecIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom =
      (unitriangularStageUnderlyingSpecIso K n r).hom ≫
        stageProductSpecRename K n r hr := by
  apply (additiveGroupAffineProductFan_isLimit K
    (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom_ext
  intro ⟨ij⟩
  exact unitriangularStage_projection_triangle K n r hr ij

/-- The full affine-space arrow, transported through the official stage
affine-space iso and the generic actual-product affine-space iso, using
Mathlib's `AffineSpace.SpecIso` on the surviving and current variables. -/
theorem unitriangularStageCoordinateMap_underlying_affineSpace (hr : 1 ≤ r) :
    (unitriangularStageUnderlyingAffineSpaceIso K n r).inv ≫
        (unitriangularStageCoordinateMap K n r hr).hom.hom ≫
        (additiveGroupProductUnderlyingAffineSpaceIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom =
      (additiveGroupAffineProductSpecToSpaceIso K (SurvivingPair n r)).symm.hom ≫
        stageProductSpecRename K n r hr ≫
        (additiveGroupAffineProductSpecToSpaceIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom := by
  rw [additiveGroupProductUnderlyingAffineSpaceIso, Iso.trans_hom]
  calc
    _ = (unitriangularStageUnderlyingAffineSpaceIso K n r).inv ≫
        (((unitriangularStageCoordinateMap K n r hr).hom.hom ≫
          (additiveGroupProductUnderlyingSpecIso K
            (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom) ≫
          (additiveGroupAffineProductSpecToSpaceIso K
            (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom) := by
              simp only [Category.assoc]
    _ = (unitriangularStageUnderlyingAffineSpaceIso K n r).inv ≫
        (((unitriangularStageUnderlyingSpecIso K n r).hom ≫
          stageProductSpecRename K n r hr) ≫
          (additiveGroupAffineProductSpecToSpaceIso K
            (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom) := by
              rw [unitriangularStageCoordinateMap_underlying_spec]
    _ = _ := by
      rw [unitriangularStageUnderlyingSpecIso, Iso.trans_hom]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, Iso.symm_hom]

/-- Kill the higher-gap variables and retain the current superdiagonal,
using Mathlib's `MvPolynomial.killCompl`. -/
def stageProductCoordinateKill (hr : 1 ≤ r) :
    MvPolynomial (SurvivingPair n r) K →ₐ[K]
      MvPolynomial (Matrix.UnitriangularGroup.superdiagonalIndex n r) K :=
  MvPolynomial.killCompl (stageSuperdiagonalInclusion_injective n r hr)

@[simp] theorem stageProductCoordinateKill_inclusion (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    stageProductCoordinateKill K n r hr
        (MvPolynomial.X (stageSuperdiagonalInclusion n r hr ij)) =
      MvPolynomial.X ij := by
  rw [← MvPolynomial.rename_X (R := K)
    (stageSuperdiagonalInclusion n r hr) ij]
  exact MvPolynomial.killCompl_rename_app
    (stageSuperdiagonalInclusion_injective n r hr) (MvPolynomial.X ij)

theorem stageProductCoordinateKill_higher (hr : 1 ≤ r)
    (s : SurvivingPair n r)
    (hs : s.1.1.1.val + r < s.1.1.2.val) :
    stageProductCoordinateKill K n r hr (MvPolynomial.X s) = 0 := by
  have hnot : s ∉ Set.range (stageSuperdiagonalInclusion n r hr) := by
    intro h
    have heq := (mem_range_stageSuperdiagonalInclusion n r hr s).1 h
    omega
  simp only [stageProductCoordinateKill, MvPolynomial.killCompl,
    MvPolynomial.aeval_X, dif_neg hnot]

/-- The coordinate-algebra pullback induced by the underlying section. -/
def stageProductSectionPullback (hr : 1 ≤ r) :
    CoordinateRing K n r →ₐ[K]
      MvPolynomial (Matrix.UnitriangularGroup.superdiagonalIndex n r) K :=
  (stageProductCoordinateKill K n r hr).comp (polynomialEquiv K n r).toAlgHom

@[simp] theorem stageProductSectionPullback_inclusion (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    stageProductSectionPullback K n r hr (coordinate K n r ij) =
      MvPolynomial.X ij := by
  change stageProductCoordinateKill K n r hr
      ((polynomialEquiv K n r) (coordinate K n r ij)) = _
  change stageProductCoordinateKill K n r hr
      ((polynomialEquiv K n r)
        (quotient K n r (entry K n ij.1.1 ij.1.2))) = _
  have hpoly := polynomialEquiv_surviving K n r
    (stageSuperdiagonalInclusion n r hr ij)
  change (polynomialEquiv K n r)
    (quotient K n r (entry K n ij.1.1 ij.1.2)) =
      MvPolynomial.X (stageSuperdiagonalInclusion n r hr ij) at hpoly
  rw [hpoly, stageProductCoordinateKill_inclusion]

theorem stageProductSectionPullback_higher (hr : 1 ≤ r)
    (s : SurvivingPair n r)
    (hs : s.1.1.1.val + r < s.1.1.2.val) :
    stageProductSectionPullback K n r hr
      (quotient K n r (entry K n s.1.1.1 s.1.1.2)) = 0 := by
  change stageProductCoordinateKill K n r hr
      ((polynomialEquiv K n r)
        (quotient K n r (entry K n s.1.1.1 s.1.1.2))) = _
  rw [polynomialEquiv_surviving, stageProductCoordinateKill_higher K n r hr s hs]

/-- The complementary-variable retraction as a genuine arrow over `Spec K`. -/
def stageProductSpecKill (hr : 1 ≤ r) :
    additiveGroupAffineProductScheme K
        (Matrix.UnitriangularGroup.superdiagonalIndex n r) ⟶
      additiveGroupAffineProductScheme K (SurvivingPair n r) :=
  (algSpec (.of K)).map
    (CommAlgCat.ofHom (stageProductCoordinateKill K n r hr)).op

/-- The spectrum maps cancel because killing the complement retracts renaming
on the entire polynomial coordinate algebra, even for empty index sets. -/
theorem stageProductSpecKill_comp_rename (hr : 1 ≤ r) :
    stageProductSpecKill K n r hr ≫ stageProductSpecRename K n r hr =
      𝟙 (additiveGroupAffineProductScheme K
        (Matrix.UnitriangularGroup.superdiagonalIndex n r)) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      (stageProductCoordinateKill K n r hr).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (MvPolynomial.rename (stageSuperdiagonalInclusion n r hr)).toRingHom) =
        𝟙 (Spec (.of (MvPolynomial
          (Matrix.UnitriangularGroup.superdiagonalIndex n r) K)))
  rw [← Spec.map_comp]
  have hkill : (stageProductCoordinateKill K n r hr).comp
      (MvPolynomial.rename (stageSuperdiagonalInclusion n r hr)) =
        AlgHom.id K (MvPolynomial
          (Matrix.UnitriangularGroup.superdiagonalIndex n r) K) :=
    MvPolynomial.killCompl_comp_rename
      (stageSuperdiagonalInclusion_injective n r hr)
  change Spec.map (CommRingCat.ofHom
      ((stageProductCoordinateKill K n r hr).comp
        (MvPolynomial.rename (stageSuperdiagonalInclusion n r hr))).toRingHom) = _
  rw [hkill]
  exact Spec.map_id _

/-- Section of the *actual* positive-stage underlying coordinate arrow;
not a morphism of group schemes. -/
def unitriangularStageCoordinateSectionOver (hr : 1 ≤ r) :
    (∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex n r =>
      additiveGroupScheme K).X ⟶ unitriangularStageUnderlyingScheme K n r :=
  (additiveGroupProductUnderlyingSpecIso K
      (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom ≫
    stageProductSpecKill K n r hr ≫
      (unitriangularStageUnderlyingSpecIso K n r).inv

/-- Reading the inverse stage-spectrum comparison on global functions recovers
the official stage polynomial algebra equivalence. -/
theorem unitriangularStageUnderlyingSpecIso_preimage_inv
    (f : CoordinateRing K n r) :
    Spec.preimage (unitriangularStageUnderlyingSpecIso K n r).inv.left f =
      polynomialEquiv K n r f := by
  change Spec.preimage
    ((AffineSpace.SpecIso (SurvivingPair n r) (.of K)).inv ≫
      (unitriangularStageUnderlyingAffineSpaceIso K n r).inv.left) f = _
  exact unitriangularStageUnderlyingAffineSpaceIso_preimage_inverse K n r f

/-- After transporting the actual section along the genuine group-product
comparison, its pullback is precisely the explicit coordinate-algebra map.
Consequently the following coordinate formulas describe this *section*, not
just an independently defined algebra homomorphism. -/
theorem unitriangularStageCoordinateSectionOver_preimage (hr : 1 ≤ r)
    (f : CoordinateRing K n r) :
    Spec.preimage
      (((additiveGroupProductUnderlyingSpecIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).inv ≫
        unitriangularStageCoordinateSectionOver K n r hr).left) f =
      stageProductSectionPullback K n r hr f := by
  have hcancel :
      (additiveGroupProductUnderlyingSpecIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).inv ≫
        unitriangularStageCoordinateSectionOver K n r hr =
      stageProductSpecKill K n r hr ≫
        (unitriangularStageUnderlyingSpecIso K n r).inv := by
    simp only [unitriangularStageCoordinateSectionOver, Iso.inv_hom_id_assoc]
  rw [hcancel, Over.comp_left, Spec.preimage_comp]
  change Spec.preimage (stageProductSpecKill K n r hr).left
      (Spec.preimage (unitriangularStageUnderlyingSpecIso K n r).inv.left f) = _
  rw [unitriangularStageUnderlyingSpecIso_preimage_inv]
  change Spec.preimage (Spec.map (CommRingCat.ofHom
      (stageProductCoordinateKill K n r hr).toRingHom))
    (polynomialEquiv K n r f) = _
  rw [Spec.preimage_map]
  rfl

/-- The actual underlying section preserves each current superdiagonal
coordinate after identifying the real group product with its polynomial
spectrum. -/
@[simp] theorem unitriangularStageCoordinateSectionOver_coordinate (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    Spec.preimage
      (((additiveGroupProductUnderlyingSpecIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).inv ≫
        unitriangularStageCoordinateSectionOver K n r hr).left)
        (coordinate K n r ij) = MvPolynomial.X ij := by
  rw [unitriangularStageCoordinateSectionOver_preimage,
    stageProductSectionPullback_inclusion]

/-- On the *actual* section, every surviving entry of gap strictly greater
than the current one pulls back to zero. -/
theorem unitriangularStageCoordinateSectionOver_higher (hr : 1 ≤ r)
    (s : SurvivingPair n r)
    (hs : s.1.1.1.val + r < s.1.1.2.val) :
    Spec.preimage
      (((additiveGroupProductUnderlyingSpecIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).inv ≫
        unitriangularStageCoordinateSectionOver K n r hr).left)
        (quotient K n r (entry K n s.1.1.1 s.1.1.2)) = 0 := by
  rw [unitriangularStageCoordinateSectionOver_preimage,
    stageProductSectionPullback_higher K n r hr s hs]

/-- The underlying section is a right inverse of the actual categorical
positive-stage group-scheme coordinate map after forgetting groups. It uses
Mathlib's `MvPolynomial.killCompl_comp_rename`; no group-scheme splitting or
published theorem of Milne is asserted. -/
theorem unitriangularStageCoordinateSectionOver_comp (hr : 1 ≤ r) :
    unitriangularStageCoordinateSectionOver K n r hr ≫
        (unitriangularStageCoordinateMap K n r hr).hom.hom =
      𝟙 ((∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex n r =>
        additiveGroupScheme K).X) := by
  apply (cancel_mono (additiveGroupProductUnderlyingSpecIso K
    (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom).mp
  rw [Category.id_comp, Category.assoc,
    unitriangularStageCoordinateMap_underlying_spec]
  unfold unitriangularStageCoordinateSectionOver
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [stageProductSpecKill_comp_rename, Category.comp_id]

end AlgebraicGeometry
