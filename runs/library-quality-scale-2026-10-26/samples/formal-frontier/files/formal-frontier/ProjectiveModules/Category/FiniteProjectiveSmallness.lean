/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.FiniteProjective
public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall

/-!
# Smallness and representatives of finite projective modules

The category `ModuleCat.FiniteProjective.{u, v} R` is essentially small in the
ring universe `u`, for independent ring and carrier universes. The proof uses
Mathlib's essentially small category of finitely generated modules and the
fully faithful inclusion supplied by `ObjectProperty.ιOfLE`.

`ModuleCat.FiniteProjective.repr` places any finite projective module in the
reference category `ModuleCat.FiniteProjective.{u, u} R`.
Its underlying carrier and linear equivalence are Mathlib's
`Module.Finite.repr` and `Module.Finite.reprEquiv`. The representative is chosen,
not canonical, but its isomorphism class is characterized by linear equivalence
of the inputs, even when their carrier universes differ. Product, zero and
`ULift` comparisons are expressed using the existing linear-equivalence API.

Essential smallness does not assert that the category with a smaller carrier
universe contains every finite projective isomorphism class. The ring-universe
reference category does represent all finite projective modules by `reprEquiv`.
All constructions work over arbitrary rings; applying them to `Rᵐᵒᵖ` gives the
corresponding interfaces for right `R`-modules.

## References and credits

This file reuses Mathlib's finite-module representatives, essentially small
finitely generated module category, skeletons and full-subcategory machinery.
It extends the finite-projective category formalization in this library.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace ModuleCat

variable (R : Type u) [Ring R]

/-- A finite projective module is finitely generated. -/
theorem isFiniteProjective_le_isFG :
    isFiniteProjective.{u, v} R ≤ isFG R :=
  fun _ h ↦ h.1

/-- Finite projective modules with any carrier universe form an essentially
small category in the ring universe. -/
instance finiteProjectiveEssentiallySmall :
    EssentiallySmall.{u} (FiniteProjective.{u, v} R) :=
  essentiallySmall_of_fully_faithful
    (ObjectProperty.ιOfLE (isFiniteProjective_le_isFG.{u, v} R))

namespace FiniteProjective

section Isomorphisms

variable {R} {X Y : FiniteProjective.{u, v} R}

/-- An isomorphism of finite projective objects gives a linear equivalence of
underlying modules. -/
def isoToLinearEquiv (e : X ≅ Y) : X ≃ₗ[R] Y :=
  ((isFiniteProjective R).ι.mapIso e).toLinearEquiv

/-- A linear equivalence of finite projective modules gives a categorical
isomorphism. -/
def isoOfLinearEquiv (e : X ≃ₗ[R] Y) : X ≅ Y :=
  (isFiniteProjective R).isoMk e.toModuleIso

@[simp]
theorem isoToLinearEquiv_apply (e : X ≅ Y) (x : X) :
    isoToLinearEquiv e x = homLinearEquiv R X Y e.hom x := rfl

@[simp]
theorem isoOfLinearEquiv_hom (e : X ≃ₗ[R] Y) :
    homLinearEquiv R X Y (isoOfLinearEquiv e).hom = e.toLinearMap := rfl

@[simp]
theorem isoOfLinearEquiv_inv (e : X ≃ₗ[R] Y) :
    homLinearEquiv R Y X (isoOfLinearEquiv e).inv = e.symm.toLinearMap := rfl

@[simp]
theorem isoToLinearEquiv_isoOfLinearEquiv (e : X ≃ₗ[R] Y) :
    isoToLinearEquiv (isoOfLinearEquiv e) = e := by
  ext x
  rfl

@[simp]
theorem isoOfLinearEquiv_isoToLinearEquiv (e : X ≅ Y) :
    isoOfLinearEquiv (isoToLinearEquiv e) = e := by
  apply Iso.ext
  apply hom_ext
  rfl

/-- Categorical isomorphism of finite projective objects is exactly linear
equivalence of their carriers. -/
theorem nonempty_iso_iff_linearEquiv :
    Nonempty (X ≅ Y) ↔ Nonempty (X ≃ₗ[R] Y) :=
  ⟨fun ⟨e⟩ ↦ ⟨isoToLinearEquiv e⟩, fun ⟨e⟩ ↦ ⟨isoOfLinearEquiv e⟩⟩

/-- Equality of skeleton classes is exactly linear equivalence. -/
theorem toSkeleton_eq_iff_linearEquiv (X Y : FiniteProjective.{u, v} R) :
    toSkeleton X = toSkeleton Y ↔ Nonempty (X ≃ₗ[R] Y) := by
  rw [toSkeleton_eq_toSkeleton_iff, nonempty_iso_iff_linearEquiv]

end Isomorphisms

section Representatives

variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

/-- A finite projective representative in the ring universe, with carrier
`Module.Finite.repr R P`. -/
noncomputable def repr : FiniteProjective.{u, u} R :=
  ⟨ModuleCat.of R (Module.Finite.repr R P),
    ⟨Module.Finite.equiv (Module.Finite.reprEquiv R P).symm,
      Module.Projective.of_equiv' (Module.Finite.reprEquiv R P).symm⟩⟩

@[simp]
theorem repr_obj : (repr R P).obj = ModuleCat.of R (Module.Finite.repr R P) := rfl

@[simp]
theorem repr_carrier : (repr R P : Type u) = Module.Finite.repr R P := rfl

/-- The chosen ring-universe representative is linearly equivalent to the
original module, in its independent carrier universe. -/
noncomputable def reprEquiv : repr R P ≃ₗ[R] P :=
  Module.Finite.reprEquiv R P

@[simp]
theorem reprEquiv_apply (x : repr R P) :
    reprEquiv R P x = Module.Finite.reprEquiv R P x := rfl

@[simp]
theorem reprEquiv_symm_apply (x : P) :
    (reprEquiv R P).symm x = (Module.Finite.reprEquiv R P).symm x := rfl

variable (Q : Type w) [AddCommGroup Q] [Module R Q]
  [Module.Finite R Q] [Module.Projective R Q]

/-- A linear equivalence of inputs in possibly different universes gives an
isomorphism between their ring-universe representatives. -/
noncomputable def reprIsoOfLinearEquiv (e : P ≃ₗ[R] Q) : repr R P ≅ repr R Q :=
  isoOfLinearEquiv ((reprEquiv R P).trans (e.trans (reprEquiv R Q).symm))

@[simp]
theorem reprIsoOfLinearEquiv_hom_apply (e : P ≃ₗ[R] Q) (x : repr R P) :
    homLinearEquiv R _ _ (reprIsoOfLinearEquiv R P Q e).hom x =
      (reprEquiv R Q).symm (e (reprEquiv R P x)) := rfl

@[simp]
theorem reprIsoOfLinearEquiv_inv_apply (e : P ≃ₗ[R] Q) (x : repr R Q) :
    homLinearEquiv R _ _ (reprIsoOfLinearEquiv R P Q e).inv x =
      (reprEquiv R P).symm (e.symm (reprEquiv R Q x)) := rfl

/-- Equality of the reference-category classes of arbitrary inputs is
characterized by linear equivalence of those inputs. -/
theorem toSkeleton_repr_eq_iff :
    toSkeleton (repr R P) = toSkeleton (repr R Q) ↔ Nonempty (P ≃ₗ[R] Q) := by
  rw [toSkeleton_eq_toSkeleton_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨(reprEquiv R P).symm.trans ((isoToLinearEquiv e).trans (reprEquiv R Q))⟩
  · rintro ⟨e⟩
    exact ⟨reprIsoOfLinearEquiv R P Q e⟩

/-- Representation is compatible with binary direct sum, modeled by the
product of the two module carriers. -/
noncomputable def reprProdIso :
    repr R (P × Q) ≅ of R (repr R P × repr R Q) :=
  isoOfLinearEquiv ((reprEquiv R (P × Q)).trans
    ((reprEquiv R P).symm.prodCongr (reprEquiv R Q).symm))

@[simp]
theorem reprProdIso_hom_apply (x : repr R (P × Q)) :
    homLinearEquiv R _ _ (reprProdIso R P Q).hom x =
      ((reprEquiv R P).symm (reprEquiv R (P × Q) x).1,
        (reprEquiv R Q).symm (reprEquiv R (P × Q) x).2) := rfl

@[simp]
theorem reprProdIso_inv_apply (x : repr R P × repr R Q) :
    homLinearEquiv R _ _ (reprProdIso R P Q).inv x =
      (reprEquiv R (P × Q)).symm (reprEquiv R P x.1, reprEquiv R Q x.2) := rfl

end Representatives

/-- Representing an object already in the reference category gives an
isomorphic object, not necessarily a definitionally equal one. -/
noncomputable def reprIso (X : FiniteProjective.{u, u} R) : repr R X ≅ X :=
  isoOfLinearEquiv (reprEquiv R X)

@[simp]
theorem reprIso_hom (X : FiniteProjective.{u, u} R) :
    homLinearEquiv R _ _ (reprIso R X).hom = (reprEquiv R X).toLinearMap := rfl

@[simp]
theorem reprIso_inv (X : FiniteProjective.{u, u} R) :
    homLinearEquiv R _ _ (reprIso R X).inv = (reprEquiv R X).symm.toLinearMap := rfl

/-- Representation leaves the skeleton class of a reference-category object
unchanged. -/
@[simp]
theorem toSkeleton_repr (X : FiniteProjective.{u, u} R) :
    toSkeleton (repr R X) = toSkeleton X :=
  congr_toSkeleton_of_iso (reprIso R X)

/-- Any subsingleton module is represented by an object isomorphic to the zero
module, without a nontriviality assumption on the ring. -/
noncomputable def reprZeroIso (Z : Type v) [AddCommGroup Z] [Module R Z]
    [Subsingleton Z] : repr R Z ≅ of R PUnit.{u + 1} :=
  isoOfLinearEquiv ((reprEquiv R Z).trans
    (LinearEquiv.ofSubsingleton Z PUnit.{u + 1}))

@[simp]
theorem reprZeroIso_hom_apply (Z : Type v) [AddCommGroup Z] [Module R Z]
    [Subsingleton Z] (x : repr R Z) :
    homLinearEquiv R _ _ (reprZeroIso R Z).hom x = PUnit.unit := rfl

@[simp]
theorem reprZeroIso_inv_apply (Z : Type v) [AddCommGroup Z] [Module R Z]
    [Subsingleton Z] (x : PUnit.{u + 1}) :
    homLinearEquiv R _ _ (reprZeroIso R Z).inv x = (reprEquiv R Z).symm 0 := rfl

/-- The skeleton class of a represented zero module is the zero-module class. -/
@[simp]
theorem toSkeleton_repr_zero (Z : Type v) [AddCommGroup Z] [Module R Z]
    [Subsingleton Z] :
    toSkeleton (repr R Z) = toSkeleton (of R PUnit.{u + 1}) :=
  congr_toSkeleton_of_iso (reprZeroIso R Z)

/-- Lifting an input carrier does not change its ring-universe representative
up to isomorphism. -/
noncomputable def reprULiftIso (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] :
    repr R (ULift.{w} P) ≅ repr R P :=
  reprIsoOfLinearEquiv R (ULift.{w} P) P ULift.moduleEquiv

@[simp]
theorem reprULiftIso_hom_apply (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] (x : repr R (ULift.{w} P)) :
    homLinearEquiv R _ _ (reprULiftIso.{u, v, w} R P).hom x =
      (reprEquiv R P).symm (reprEquiv R (ULift.{w} P) x).down := rfl

@[simp]
theorem reprULiftIso_inv_apply (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] (x : repr R P) :
    homLinearEquiv R _ _ (reprULiftIso.{u, v, w} R P).inv x =
      (reprEquiv R (ULift.{w} P)).symm ⟨reprEquiv R P x⟩ := rfl

/-- The skeleton class of a representative is invariant under carrier lift. -/
@[simp]
theorem toSkeleton_repr_ulift (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] :
    toSkeleton (repr R (ULift.{w} P)) = toSkeleton (repr R P) :=
  congr_toSkeleton_of_iso (reprULiftIso R P)

section IsomorphismClasses

variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

/-- The isomorphism class of an arbitrary finite projective module in the
skeleton of the ring-universe reference category. -/
noncomputable def isoClass : Skeleton (FiniteProjective.{u, u} R) :=
  toSkeleton (repr R P)

/-- The class is computed from the chosen ring-universe representative. -/
theorem isoClass_eq_toSkeleton_repr : isoClass R P = toSkeleton (repr R P) := rfl

/-- Classes of inputs with independent carrier universes agree exactly when
those inputs are linearly equivalent. Both classes lie in the same skeleton. -/
theorem isoClass_eq_iff (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q] :
    isoClass R P = isoClass R Q ↔ Nonempty (P ≃ₗ[R] Q) :=
  toSkeleton_repr_eq_iff R P Q

/-- On reference-category objects, `isoClass` is the existing skeleton map. -/
@[simp]
theorem isoClass_of (X : FiniteProjective.{u, u} R) :
    isoClass R X = toSkeleton X :=
  toSkeleton_repr R X

/-- Lifting the carrier does not change its class in the reference skeleton. -/
@[simp]
theorem isoClass_ulift : isoClass R (ULift.{w} P) = isoClass R P :=
  toSkeleton_repr_ulift R P

/-- Subsingleton modules have the zero-module class, over any ring. -/
@[simp]
theorem isoClass_zero (Z : Type v) [AddCommGroup Z] [Module R Z] [Subsingleton Z] :
    isoClass R Z = toSkeleton (of R PUnit.{u + 1}) :=
  toSkeleton_repr_zero R Z

end IsomorphismClasses

end FiniteProjective

end ModuleCat
