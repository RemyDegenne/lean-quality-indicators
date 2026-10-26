/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Translation
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Closed points of group schemes

This file relates the group of rational points of a finite-type group scheme
over an algebraically closed field to its closed points. It also restricts
inversion and left translation to homeomorphisms of the closed-point subspace.

No topological-group structure is asserted: continuity of scheme-theoretic
multiplication uses the scheme-product topology, which need not be the ordinary
product topology on the closed-point spaces.

## References

- James S. Milne, *Algebraic Groups* (2017), items 1.7 and 1.8:
  the rational-point group, its identification with closed points over an
  algebraically closed field, and inversion and translation on those points.
- Mathlib, `AlgebraicGeometry.pointEquivClosedPoint`
  (`Mathlib.AlgebraicGeometry.AlgClosed.Basic`): the equivalence between
  base-preserving rational points and closed points of a locally-finite-type
  scheme over an algebraically closed field.
- Mathlib, `schemeIsoToHomeo`: the underlying homeomorphism of a scheme
  isomorphism. Left translation uses `CategoryTheory.GrpObj.mulLeft` from
  `AlgebraicGroups.GroupObject.Translation`, built from Mathlib's
  `CategoryTheory.GrpObj.mulRight`.
-/

public section

open CategoryTheory Limits
open CategoryTheory.MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {G : Scheme.{u}}

/-- Morphisms from the terminal object of `Over (Spec K)` are exactly
base-preserving scheme-valued `K`-points, as in Milne's affine-point convention
in *Algebraic Groups* (2017), item 1.4. -/
@[expose]
def groupSchemePointEquiv (f : G ⟶ Spec (.of K)) :
    (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) ≃
      {p : Spec (.of K) ⟶ G // p ≫ f = 𝟙 _} where
  toFun p := ⟨p.left, by simpa using p.w⟩
  invFun p := Over.homMk p.1 (by simpa using p.2)
  left_inv p := by ext; rfl
  right_inv p := by ext; rfl

/-- Over an algebraically closed field, the group-scheme-valued points are in
bijection with the closed points, as in Milne, *Algebraic Groups* (2017),
item 1.7, using Mathlib's `pointEquivClosedPoint`. -/
@[expose]
def groupSchemePointEquivClosedPoint (f : G ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [IsAlgClosed K] :
    (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) ≃ closedPoints G :=
  (groupSchemePointEquiv f).trans (pointEquivClosedPoint f)

/-- Evaluating the closed point associated to a group-scheme-valued point
recovers its underlying point. -/
@[simp]
lemma groupSchemePointEquivClosedPoint_apply_value (f : G ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [IsAlgClosed K]
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) :
    (groupSchemePointEquivClosedPoint f x).1 =
      x.left (IsLocalRing.closedPoint K) :=
  rfl

/-- The rational point associated to a closed point evaluates back to that
closed point. -/
@[simp]
lemma groupSchemePointEquivClosedPoint_symm_apply_value
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsAlgClosed K]
    (x : closedPoints G) :
    ((groupSchemePointEquivClosedPoint f).symm x).left
        (IsLocalRing.closedPoint K) = x.1 := by
  change (groupSchemePointEquivClosedPoint f
    ((groupSchemePointEquivClosedPoint f).symm x)).1 = x.1
  exact congrArg Subtype.val
    ((groupSchemePointEquivClosedPoint f).apply_symm_apply x)

/-- The abstract group structure on the closed points transported from the
group of rational points, as in Milne, *Algebraic Groups* (2017), item 1.7.
This is deliberately not a global instance. -/
abbrev groupSchemeClosedPointsGroup (f : G ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [IsAlgClosed K] [GrpObj (Over.mk f)] :
    Group (closedPoints G) :=
  Equiv.group (groupSchemePointEquivClosedPoint f).symm

/-- With the transported group structure, the equivalence from rational points
to closed points is an equivalence of groups, as in Milne, *Algebraic Groups*
(2017), item 1.7. -/
def groupSchemePointMulEquivClosedPoint (f : G ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [IsAlgClosed K] [GrpObj (Over.mk f)] :
    letI := groupSchemeClosedPointsGroup f
    (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) ≃* closedPoints G := by
  letI := groupSchemeClosedPointsGroup f
  exact (Equiv.mulEquiv (groupSchemePointEquivClosedPoint f).symm).symm

/-- A scheme isomorphism restricts to a homeomorphism of closed-point
subspaces, using Mathlib's `schemeIsoToHomeo`. -/
def closedPointsHomeomorphOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    closedPoints X ≃ₜ closedPoints Y :=
  e.schemeIsoToHomeo.subtype fun x ↦ by
    simpa using (e.schemeIsoToHomeo.isClosed_image (s := {x})).symm

/-- Inversion in a group scheme is a homeomorphism of its closed-point
subspace without a finite-type or algebraic-closure assumption. For finite-type
group schemes over an algebraically closed field this is the inversion in
Milne, *Algebraic Groups* (2017), item 1.7. -/
def groupSchemeInvClosedPointsHomeomorph (f : G ⟶ Spec (.of K))
    [GrpObj (Over.mk f)] : closedPoints G ≃ₜ closedPoints G :=
  closedPointsHomeomorphOfIso ((Over.forget _).mapIso (asIso ι[Over.mk f]))

/-- Left translation by a rational point of a group scheme is a homeomorphism
of its closed-point subspace without a finite-type or algebraic-closure
assumption. For finite-type group schemes over an algebraically closed field
this specializes to Milne, *Algebraic Groups* (2017), items 1.7–1.8. -/
def groupSchemeMulLeftClosedPointsHomeomorph (f : G ⟶ Spec (.of K))
    [GrpObj (Over.mk f)]
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) :
    closedPoints G ≃ₜ closedPoints G :=
  closedPointsHomeomorphOfIso
    ((Over.forget _).mapIso (CategoryTheory.GrpObj.mulLeft a))

/-- On closed points represented by rational points, the inversion
homeomorphism acts by the rational-point group inverse. -/
@[simp]
lemma groupSchemeInvClosedPointsHomeomorph_apply_point (f : G ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [IsAlgClosed K] [GrpObj (Over.mk f)]
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) :
    groupSchemeInvClosedPointsHomeomorph f (groupSchemePointEquivClosedPoint f x) =
      groupSchemePointEquivClosedPoint f x⁻¹ := by
  apply Subtype.ext
  change (asIso ι[Over.mk f]).hom.left (x.left (IsLocalRing.closedPoint K)) =
    x⁻¹.left (IsLocalRing.closedPoint K)
  rfl

/-- On closed points represented by rational points, the left-translation
homeomorphism acts by left multiplication in the rational-point group. -/
@[simp]
lemma groupSchemeMulLeftClosedPointsHomeomorph_apply_point
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsAlgClosed K]
    [GrpObj (Over.mk f)]
    (a x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) :
    groupSchemeMulLeftClosedPointsHomeomorph f a
        (groupSchemePointEquivClosedPoint f x) =
      groupSchemePointEquivClosedPoint f (a * x) := by
  apply Subtype.ext
  change (CategoryTheory.GrpObj.mulLeft a).hom.left
      (x.left (IsLocalRing.closedPoint K)) =
    (a * x).left (IsLocalRing.closedPoint K)
  exact congrArg
    (fun z : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f =>
      z.left (IsLocalRing.closedPoint K))
    (CategoryTheory.GrpObj.comp_mulLeft_hom a x)

/-- Any two closed points of a group scheme locally of finite type over an
algebraically closed field are related by an automorphism over the base, using
the left translations of Milne, *Algebraic Groups* (2017), item 1.8. -/
theorem exists_groupSchemeIso_map_closedPoint (f : G ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [IsAlgClosed K] [GrpObj (Over.mk f)]
    (x y : closedPoints G) :
    ∃ e : Over.mk f ≅ Over.mk f, e.hom.left x.1 = y.1 := by
  let E := groupSchemePointEquivClosedPoint f
  let a := E.symm y * (E.symm x)⁻¹
  refine ⟨CategoryTheory.GrpObj.mulLeft a, ?_⟩
  have h := groupSchemeMulLeftClosedPointsHomeomorph_apply_point f a (E.symm x)
  have h' : groupSchemeMulLeftClosedPointsHomeomorph f a x = y := by
    simpa [E, a] using h
  exact congrArg Subtype.val h'

end AlgebraicGeometry
