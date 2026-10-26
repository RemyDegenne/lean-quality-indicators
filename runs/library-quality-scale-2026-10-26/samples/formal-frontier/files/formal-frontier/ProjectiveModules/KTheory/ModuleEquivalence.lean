/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.ModuleEquivalence
public import ProjectiveModules.Category.ChangeOfRings
public import ProjectiveModules.KTheory.K0
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# K₀ and equivalences of right-module categories

An ordinary equivalence of right-module categories induces additive equivalences
of their finite-projective class monoids and K₀ groups. The scalar universes
`uR`, `uS` and carrier parameters `vR`, `vS` are independent; the categories have
carrier heights `max uR vR` and `max uS vS`. Right modules are modules over the
opposite rings, not objects of opposite categories.

The class construction uses ring-universe representatives, lifts their carriers
to the supported source height, then applies the functor. The inverse uses the
same construction for the inverse equivalence. The K₀ construction uses the
additive localization of the class monoid at its top submonoid. Its forward
homomorphism is characterized by the group-completion universal property.
No scalar linearity, commutativity or cancellation is assumed.

## References and credits

* C. A. Weibel, *The K-book*, Chapter II: finite-projective right modules and K₀.
* Formal Frontier Agents' Projective Modules: representatives, class descent,
  finite-projective preservation and K₀'s universal property.
* Mathlib's full-subcategory equivalence, ULift and localization formalizations;
  Alex J. Best and Yaël Dillies' Grothendieck-group formalization.
* Yunzhou Xie and Jujian Zhang's matrix-Morita formalization, Mathlib's
  matrix/opposite conversion, change of rings and right matrix action.
-/

@[expose] public section

open CategoryTheory

universe uR uS uT vR vS vT w

namespace KTheory

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

-- Restrict the equivalence to the full subcategories of finite projective modules.
private noncomputable def finiteProjectiveEquivalence
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ) :
    ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ ≌
      ModuleCat.FiniteProjective.{uS, max uS vS} Sᵐᵒᵖ :=
  e.congrFullSubcategory (by
    funext X
    exact propext
      (ModuleCat.isFiniteProjective_iff_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e X))

namespace ProjectiveClass

-- The class lift takes ring-sized objects; lift their carriers before applying e.
private noncomputable def classImage
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)
    (X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ) : ProjectiveClass S :=
  ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj
    (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} X)))

private theorem classImage_iso
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)
    {X Y : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ} (i : X ≅ Y) :
    classImage e X = classImage e Y := by
  let i' :
      ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} X) ≅
        ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} Y) :=
    (ModuleCat.isFiniteProjective Rᵐᵒᵖ).isoMk
      ((ModuleCat.uliftFunctor.{vR} Rᵐᵒᵖ).mapIso
        ((ModuleCat.isFiniteProjective Rᵐᵒᵖ).ι.mapIso i))
  exact of_eq_of_equiv S
    ((finiteProjectiveEquivalence e).functor.obj
      (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} X)))
    (ModuleCat.FiniteProjective.isoToLinearEquiv
      ((finiteProjectiveEquivalence e).functor.mapIso i'))

private theorem classImage_zero
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ) :
    classImage e (ModuleCat.FiniteProjective.of Rᵐᵒᵖ PUnit.{uR + 1}) = 0 := by
  let Z := (finiteProjectiveEquivalence e).functor.obj
    (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} PUnit.{uR + 1}))
  have hzero : Limits.IsZero
      (ModuleCat.of Rᵐᵒᵖ (ULift.{vR} PUnit.{uR + 1})) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have hZ : Limits.IsZero Z.obj := e.functor.map_isZero hzero
  let : Subsingleton Z := ModuleCat.isZero_iff_subsingleton.mp hZ
  exact (of_eq_of_equiv S Z
    (LinearEquiv.ofSubsingleton Z PUnit.{uS + 1})).trans (of_zero S _)

private theorem classImage_add
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)
    (X Y : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ) :
    classImage e (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) =
      classImage e X + classImage e Y := by
  let X₁ := ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} X)
  let Y₁ := ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} Y)
  let X₂ := (finiteProjectiveEquivalence e).functor.obj X₁
  let Y₂ := (finiteProjectiveEquivalence e).functor.obj Y₁
  let Z₂ := (finiteProjectiveEquivalence e).functor.obj
    (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} (X × Y)))
  let p : ModuleCat.of Rᵐᵒᵖ (ULift.{vR} (X × Y)) ≅
      ModuleCat.of Rᵐᵒᵖ (X₁ × Y₁) :=
    (show ULift.{vR} (X × Y) ≃ₗ[Rᵐᵒᵖ] (X₁ × Y₁) from
      ULift.moduleEquiv.trans
        (ULift.moduleEquiv.symm.prodCongr ULift.moduleEquiv.symm)).toModuleIso
  -- Equivalences preserve products; no additivity or scalar linearity is needed.
  let : Limits.PreservesBinaryBiproducts e.functor :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryProducts e.functor
  let q : Z₂.obj ≅ ModuleCat.of Sᵐᵒᵖ (X₂ × Y₂) :=
    e.functor.mapIso p ≪≫
      e.functor.mapIso (ModuleCat.biprodIsoProd X₁.obj Y₁.obj).symm ≪≫
      e.functor.mapBiprod X₁.obj Y₁.obj ≪≫
      ModuleCat.biprodIsoProd X₂.obj Y₂.obj
  exact (of_eq_of_equiv S Z₂ q.toLinearEquiv).trans (of_prod S X₂ Y₂)

private noncomputable def classMap
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ) :
    ProjectiveClass R →+ ProjectiveClass S :=
  ProjectiveClass.lift R (classImage e)
    (classImage_iso e) (classImage_zero e) (classImage_add e)

-- Both sides have the supported source height, so this is a ModuleCat isomorphism.
private noncomputable def supportedReprIso
    (X : ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ) :
    ModuleCat.of Rᵐᵒᵖ
        (ULift.{vR} (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ X)) ≅ X.obj :=
  (ULift.moduleEquiv.trans (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ X)).toModuleIso

-- These evaluations use the old class lift, before constructing an AddEquiv.
private theorem classMap_of_reference
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)
    (X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ) :
    classMap e (ProjectiveClass.of R X) =
      ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj
        (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} X))) := by
  exact ProjectiveClass.lift_of R (classImage e)
    (classImage_iso e) (classImage_zero e) (classImage_add e) X

private theorem classMap_of_module
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)
    (M : Type w) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    classMap e (ProjectiveClass.of R M) =
      ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj
        (ModuleCat.FiniteProjective.of Rᵐᵒᵖ
          (ULift.{vR} (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M)))) := by
  exact ProjectiveClass.lift_of_module (R := R) (M := M) (f := classImage e)
    (hiso := classImage_iso e) (hzero := classImage_zero e) (hadd := classImage_add e)

private theorem classMap_of
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)
    (X : ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ) :
    classMap e (ProjectiveClass.of R X) =
      ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj X) := by
  calc
    classMap e (ProjectiveClass.of R X) =
        ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj
          (ModuleCat.FiniteProjective.of Rᵐᵒᵖ
            (ULift.{vR} (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ X)))) :=
      classMap_of_module e X
    _ = ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj X) :=
      ProjectiveClass.of_eq_of_equiv S
        ((finiteProjectiveEquivalence e).functor.obj
          (ModuleCat.FiniteProjective.of Rᵐᵒᵖ
            (ULift.{vR} (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ X))))
        (N := (finiteProjectiveEquivalence e).functor.obj X)
        (e.functor.mapIso (supportedReprIso X)).toLinearEquiv

/-- The additive equivalence of finite-projective right-module classes induced
by an equivalence of right-module categories, as in Morita invariance of
finite projective modules in Weibel's *The K-book*, Chapter II. -/
@[no_expose] noncomputable def equivOfModuleEquivalence
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ) :
    ProjectiveClass R ≃+ ProjectiveClass S where
  toFun := classMap e
  invFun := classMap (R := S) (S := R)
    (show ModuleCat.{max uS vS} Sᵐᵒᵖ ≌ ModuleCat.{max uR vR} Rᵐᵒᵖ from e.symm)
  left_inv := by
    intro a
    refine ProjectiveClass.induction_on R a ?_
    intro X
    let X' : ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ :=
      ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} X)
    calc
      classMap e.symm (classMap e (ProjectiveClass.of R X)) =
          classMap e.symm
            (ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj X')) :=
        congrArg (classMap e.symm) (classMap_of_reference e X)
      _ = ProjectiveClass.of R ((finiteProjectiveEquivalence e.symm).functor.obj
          ((finiteProjectiveEquivalence e).functor.obj X')) :=
        classMap_of e.symm ((finiteProjectiveEquivalence e).functor.obj X')
      _ = ProjectiveClass.of R X' :=
        ProjectiveClass.of_eq_of_equiv R
          ((finiteProjectiveEquivalence e.symm).functor.obj
            ((finiteProjectiveEquivalence e).functor.obj X'))
          (N := X') (e.unitIso.app X'.obj).symm.toLinearEquiv
      _ = ProjectiveClass.of R X := ProjectiveClass.of_ulift R X
  right_inv := by
    intro b
    refine ProjectiveClass.induction_on S b ?_
    intro Y
    let Y' : ModuleCat.FiniteProjective.{uS, max uS vS} Sᵐᵒᵖ :=
      ModuleCat.FiniteProjective.of Sᵐᵒᵖ (ULift.{vS} Y)
    calc
      classMap e (classMap e.symm (ProjectiveClass.of S Y)) =
          classMap e
            (ProjectiveClass.of R ((finiteProjectiveEquivalence e.symm).functor.obj Y')) :=
        congrArg (classMap e) (classMap_of_reference e.symm Y)
      _ = ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj
          ((finiteProjectiveEquivalence e.symm).functor.obj Y')) :=
        classMap_of e ((finiteProjectiveEquivalence e.symm).functor.obj Y')
      _ = ProjectiveClass.of S Y' :=
        ProjectiveClass.of_eq_of_equiv S
          ((finiteProjectiveEquivalence e).functor.obj
            ((finiteProjectiveEquivalence e.symm).functor.obj Y'))
          (N := Y') (e.counitIso.app Y'.obj).toLinearEquiv
      _ = ProjectiveClass.of S Y := ProjectiveClass.of_ulift S Y
  map_add' := (classMap e).map_add

variable (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)

-- Supply the carrier's finite/projective instances explicitly for anonymous bundles.
/-- On a supported finite-projective object, transport is its functor image. -/
theorem equivOfModuleEquivalence_of
    (X : ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ) :
    equivOfModuleEquivalence e (ProjectiveClass.of R X) =
      @ProjectiveClass.of S _
        (⟨e.functor.obj X.obj,
          ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e X.obj X.property⟩ :
          ModuleCat.FiniteProjective.{uS, max uS vS} Sᵐᵒᵖ) _ _
        (ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e X.obj X.property).1
        (ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e X.obj X.property).2 := by
  exact classMap_of e X

/-- An arbitrary carrier is represented in the ring universe, then lifted to
the supported source height before applying the functor. -/
theorem equivOfModuleEquivalence_of_module (M : Type w)
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    equivOfModuleEquivalence e (ProjectiveClass.of R M) =
      @ProjectiveClass.of S _
        (⟨e.functor.obj (ModuleCat.of Rᵐᵒᵖ
            (ULift.{vR} (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M))),
          ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e _
            ⟨inferInstance, inferInstance⟩⟩ :
          ModuleCat.FiniteProjective.{uS, max uS vS} Sᵐᵒᵖ) _ _
        (ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e
          (ModuleCat.of Rᵐᵒᵖ (ULift.{vR} (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M)))
          ⟨inferInstance, inferInstance⟩).1
        (ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e
          (ModuleCat.of Rᵐᵒᵖ (ULift.{vR} (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M)))
          ⟨inferInstance, inferInstance⟩).2 := by
  exact classMap_of_module e M

/-- Restriction along a ring equivalence preserves the regular right-module
class, represented by the canonical left regular modules over the opposite rings.
The supported lifts allow the two rings to have independent universes. -/
theorem equivOfModuleEquivalence_restrictScalars_regular (f : R ≃+* S) :
    equivOfModuleEquivalence.{uS, uR, uR, uS}
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.op) (of S Sᵐᵒᵖ) =
      of R Rᵐᵒᵖ := by
  let X : ModuleCat.FiniteProjective.{uS, max uR uS} Sᵐᵒᵖ :=
    ModuleCat.FiniteProjective.of Sᵐᵒᵖ (ULift.{uR} Sᵐᵒᵖ)
  let Y : ModuleCat.FiniteProjective.{uR, max uR uS} Rᵐᵒᵖ :=
    (finiteProjectiveEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.op)).functor.obj X
  have hX : of S Sᵐᵒᵖ = of S X := (of_ulift S Sᵐᵒᵖ).symm
  calc
    equivOfModuleEquivalence.{uS, uR, uR, uS}
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.op) (of S Sᵐᵒᵖ) =
        of R Y := by
      rw [hX]
      exact equivOfModuleEquivalence_of _ X
    _ = of R (ULift.{uS} Rᵐᵒᵖ) :=
      of_eq_of_equiv R Y
        (ModuleCat.restrictScalarsUliftIsoOfEquiv f.op).toLinearEquiv
    _ = of R Rᵐᵒᵖ := of_ulift R Rᵐᵒᵖ

/-- Inverse transport is transport along the inverse category equivalence. -/
theorem equivOfModuleEquivalence_symm :
    (equivOfModuleEquivalence e).symm =
      equivOfModuleEquivalence (R := S) (S := R) e.symm := by
  apply AddEquiv.ext
  intro b
  rfl

/-- Inverse evaluation on a supported target object uses the inverse functor. -/
theorem equivOfModuleEquivalence_symm_of
    (Y : ModuleCat.FiniteProjective.{uS, max uS vS} Sᵐᵒᵖ) :
    (equivOfModuleEquivalence e).symm (ProjectiveClass.of S Y) =
      @ProjectiveClass.of R _
        (⟨e.symm.functor.obj Y.obj,
          ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm Y.obj Y.property⟩ :
          ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ) _ _
        (ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm Y.obj Y.property).1
        (ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm Y.obj Y.property).2 := by
  exact classMap_of e.symm Y

/-- Inverse evaluation on arbitrary target carriers normalizes at the target
ring height, then lifts to the inverse functor's supported source height. -/
theorem equivOfModuleEquivalence_symm_of_module (N : Type w)
    [AddCommGroup N] [Module Sᵐᵒᵖ N]
    [Module.Finite Sᵐᵒᵖ N] [Module.Projective Sᵐᵒᵖ N] :
    (equivOfModuleEquivalence e).symm (ProjectiveClass.of S N) =
      @ProjectiveClass.of R _
        (⟨e.symm.functor.obj (ModuleCat.of Sᵐᵒᵖ
            (ULift.{vS} (ModuleCat.FiniteProjective.repr Sᵐᵒᵖ N))),
          ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm _
            ⟨inferInstance, inferInstance⟩⟩ :
          ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ) _ _
        (ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm
          (ModuleCat.of Sᵐᵒᵖ (ULift.{vS} (ModuleCat.FiniteProjective.repr Sᵐᵒᵖ N)))
          ⟨inferInstance, inferInstance⟩).1
        (ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm
          (ModuleCat.of Sᵐᵒᵖ (ULift.{vS} (ModuleCat.FiniteProjective.repr Sᵐᵒᵖ N)))
          ⟨inferInstance, inferInstance⟩).2 := by
  exact classMap_of_module e.symm N

/-- Identity transport is the identity additive equivalence. -/
theorem equivOfModuleEquivalence_refl :
    equivOfModuleEquivalence
        (CategoryTheory.Equivalence.refl (C := ModuleCat.{max uR vR} Rᵐᵒᵖ)) =
      AddEquiv.refl (ProjectiveClass R) := by
  apply AddEquiv.ext
  intro a
  refine ProjectiveClass.induction_on R a ?_
  intro X
  change classMap (CategoryTheory.Equivalence.refl
    (C := ModuleCat.{max uR vR} Rᵐᵒᵖ)) (ProjectiveClass.of R X) = ProjectiveClass.of R X
  exact (classMap_of_reference (CategoryTheory.Equivalence.refl
    (C := ModuleCat.{max uR vR} Rᵐᵒᵖ)) X).trans (ProjectiveClass.of_ulift R X)

/-- Composition uses the same supported middle module category on both sides. -/
theorem equivOfModuleEquivalence_trans {T : Type uT} [Ring T]
    (d : ModuleCat.{max uS vS} Sᵐᵒᵖ ≌ ModuleCat.{max uT vT} Tᵐᵒᵖ) :
    equivOfModuleEquivalence (e.trans d) =
      (equivOfModuleEquivalence e).trans (equivOfModuleEquivalence d) := by
  apply AddEquiv.ext
  intro a
  refine ProjectiveClass.induction_on R a ?_
  intro X
  let X' : ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ :=
    ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} X)
  change classMap (e.trans d) (ProjectiveClass.of R X) =
    classMap d (classMap e (ProjectiveClass.of R X))
  calc
    classMap (e.trans d) (ProjectiveClass.of R X) =
        ProjectiveClass.of T ((finiteProjectiveEquivalence (e.trans d)).functor.obj X') :=
      classMap_of_reference (e.trans d) X
    _ = classMap d
        (ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj X')) :=
      (classMap_of d ((finiteProjectiveEquivalence e).functor.obj X')).symm
    _ = classMap d (classMap e (ProjectiveClass.of R X)) :=
      congrArg (classMap d) (classMap_of_reference e X).symm

/-- Naturally isomorphic functors induce the same additive equivalence. -/
theorem equivOfModuleEquivalence_congr
    (e' : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)
    (α : e.functor ≅ e'.functor) :
    equivOfModuleEquivalence e = equivOfModuleEquivalence e' := by
  apply AddEquiv.ext
  intro a
  refine ProjectiveClass.induction_on R a ?_
  intro X
  let X' : ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ :=
    ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} X)
  change classMap e (ProjectiveClass.of R X) = classMap e' (ProjectiveClass.of R X)
  calc
    classMap e (ProjectiveClass.of R X) =
        ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj X') :=
      classMap_of_reference e X
    _ = ProjectiveClass.of S ((finiteProjectiveEquivalence e').functor.obj X') :=
      ProjectiveClass.of_eq_of_equiv S ((finiteProjectiveEquivalence e).functor.obj X')
        (N := (finiteProjectiveEquivalence e').functor.obj X') (α.app X'.obj).toLinearEquiv
    _ = classMap e' (ProjectiveClass.of R X) := (classMap_of_reference e' X).symm

end ProjectiveClass

namespace K0

private theorem classEquivalence_map_top
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ) :
    (⊤ : AddSubmonoid (ProjectiveClass R)).map
        (ProjectiveClass.equivOfModuleEquivalence e).toAddMonoidHom =
      (⊤ : AddSubmonoid (ProjectiveClass S)) := by
  apply le_antisymm le_top
  intro b _
  obtain ⟨a, ha⟩ := (ProjectiveClass.equivOfModuleEquivalence e).surjective b
  exact AddSubmonoid.mem_map.mpr ⟨a, AddSubmonoid.mem_top a, ha⟩

/-- The additive equivalence on K₀ induced by an equivalence of right-module
categories, using the localization of the class monoid. This is Morita
invariance of K₀; see Weibel's *The K-book*, Chapter II. -/
noncomputable def equivOfModuleEquivalence
    (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ) : K0 R ≃+ K0 S :=
  (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R))).addEquivOfAddEquiv
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass S)))
    (j := ProjectiveClass.equivOfModuleEquivalence e)
    (by exact classEquivalence_map_top e)

variable (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)

/-- The completion square commutes on every projective class. -/
theorem equivOfModuleEquivalence_ofClass (a : ProjectiveClass R) :
    equivOfModuleEquivalence e (K0.ofClass R a) =
      K0.ofClass S (ProjectiveClass.equivOfModuleEquivalence e a) := by
  exact AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R)))
    (k := AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass S)))
    (j := ProjectiveClass.equivOfModuleEquivalence e)
    (classEquivalence_map_top e) a

/-- The whole forward hom is the K₀ universal extension of the class map. -/
theorem equivOfModuleEquivalence_toAddMonoidHom :
    (equivOfModuleEquivalence e).toAddMonoidHom =
      K0.lift R ((K0.ofClass S).comp
        (ProjectiveClass.equivOfModuleEquivalence e).toAddMonoidHom) := by
  apply K0.hom_ext_ofClass R
  intro a
  simpa only [K0.lift_ofClass, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] using
    equivOfModuleEquivalence_ofClass e a

/-- Supported module generators are sent to the generators of their images. -/
theorem equivOfModuleEquivalence_of
    (X : ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ) :
    equivOfModuleEquivalence e (K0.of R X) =
      @K0.of S _
        (⟨e.functor.obj X.obj,
          ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e X.obj X.property⟩ :
          ModuleCat.FiniteProjective.{uS, max uS vS} Sᵐᵒᵖ) _ _
        (ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e X.obj X.property).1
        (ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e X.obj X.property).2 := by
  rw [← K0.ofClass_of R X, equivOfModuleEquivalence_ofClass,
    ProjectiveClass.equivOfModuleEquivalence_of e X, K0.ofClass_of]

/-- Module generators in any carrier universe use repr then supported ULift. -/
theorem equivOfModuleEquivalence_of_module (M : Type w)
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    equivOfModuleEquivalence e (K0.of R M) =
      @K0.of S _
        (⟨e.functor.obj (ModuleCat.of Rᵐᵒᵖ
            (ULift.{vR} (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M))),
          ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e _
            ⟨inferInstance, inferInstance⟩⟩ :
          ModuleCat.FiniteProjective.{uS, max uS vS} Sᵐᵒᵖ) _ _
        (ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e
          (ModuleCat.of Rᵐᵒᵖ (ULift.{vR} (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M)))
          ⟨inferInstance, inferInstance⟩).1
        (ModuleCat.isFiniteProjective_of_equivalence Rᵐᵒᵖ Sᵐᵒᵖ e
          (ModuleCat.of Rᵐᵒᵖ (ULift.{vR} (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M)))
          ⟨inferInstance, inferInstance⟩).2 := by
  rw [← K0.ofClass_of R M, equivOfModuleEquivalence_ofClass,
    ProjectiveClass.equivOfModuleEquivalence_of_module e M, K0.ofClass_of]

/-- Inverting the K₀ map is transport along the inverse category equivalence. -/
theorem equivOfModuleEquivalence_symm :
    (equivOfModuleEquivalence e).symm =
      equivOfModuleEquivalence (R := S) (S := R) e.symm := by
  apply AddEquiv.toAddMonoidHom_injective
  apply K0.hom_ext_ofClass S
  intro b
  apply (equivOfModuleEquivalence e).injective
  simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply,
    equivOfModuleEquivalence_ofClass, ← ProjectiveClass.equivOfModuleEquivalence_symm e]

/-- The inverse completion square commutes on every target class. -/
theorem equivOfModuleEquivalence_symm_ofClass (b : ProjectiveClass S) :
    (equivOfModuleEquivalence e).symm (K0.ofClass S b) =
      K0.ofClass R ((ProjectiveClass.equivOfModuleEquivalence e).symm b) := by
  rw [equivOfModuleEquivalence_symm, equivOfModuleEquivalence_ofClass,
    ProjectiveClass.equivOfModuleEquivalence_symm]

/-- Inverse generator evaluation uses the inverse functor at the target height. -/
theorem equivOfModuleEquivalence_symm_of
    (Y : ModuleCat.FiniteProjective.{uS, max uS vS} Sᵐᵒᵖ) :
    (equivOfModuleEquivalence e).symm (K0.of S Y) =
      @K0.of R _
        (⟨e.symm.functor.obj Y.obj,
          ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm Y.obj Y.property⟩ :
          ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ) _ _
        (ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm Y.obj Y.property).1
        (ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm Y.obj Y.property).2 := by
  rw [← K0.ofClass_of S Y, equivOfModuleEquivalence_symm_ofClass,
    ProjectiveClass.equivOfModuleEquivalence_symm_of e Y, K0.ofClass_of]

/-- Inverse K₀ generator evaluation for arbitrary target carriers uses repr
then ULift at the supported target height, never the raw arbitrary carrier. -/
theorem equivOfModuleEquivalence_symm_of_module (N : Type w)
    [AddCommGroup N] [Module Sᵐᵒᵖ N]
    [Module.Finite Sᵐᵒᵖ N] [Module.Projective Sᵐᵒᵖ N] :
    (equivOfModuleEquivalence e).symm (K0.of S N) =
      @K0.of R _
        (⟨e.symm.functor.obj (ModuleCat.of Sᵐᵒᵖ
            (ULift.{vS} (ModuleCat.FiniteProjective.repr Sᵐᵒᵖ N))),
          ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm _
            ⟨inferInstance, inferInstance⟩⟩ :
          ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ) _ _
        (ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm
          (ModuleCat.of Sᵐᵒᵖ (ULift.{vS} (ModuleCat.FiniteProjective.repr Sᵐᵒᵖ N)))
          ⟨inferInstance, inferInstance⟩).1
        (ModuleCat.isFiniteProjective_of_equivalence Sᵐᵒᵖ Rᵐᵒᵖ e.symm
          (ModuleCat.of Sᵐᵒᵖ (ULift.{vS} (ModuleCat.FiniteProjective.repr Sᵐᵒᵖ N)))
          ⟨inferInstance, inferInstance⟩).2 := by
  rw [← K0.ofClass_of S N, equivOfModuleEquivalence_symm_ofClass,
    ProjectiveClass.equivOfModuleEquivalence_symm_of_module e N, K0.ofClass_of]

/-- Identity module-category transport is the identity on K₀. -/
theorem equivOfModuleEquivalence_refl :
    equivOfModuleEquivalence
        (CategoryTheory.Equivalence.refl (C := ModuleCat.{max uR vR} Rᵐᵒᵖ)) =
      AddEquiv.refl (K0 R) := by
  apply AddEquiv.toAddMonoidHom_injective
  apply K0.hom_ext_ofClass R
  intro a
  simp only [AddEquiv.coe_toAddMonoidHom, equivOfModuleEquivalence_ofClass,
    ProjectiveClass.equivOfModuleEquivalence_refl, AddEquiv.refl_apply]

/-- K₀ transport respects composition with the exact same middle height. -/
theorem equivOfModuleEquivalence_trans {T : Type uT} [Ring T]
    (d : ModuleCat.{max uS vS} Sᵐᵒᵖ ≌ ModuleCat.{max uT vT} Tᵐᵒᵖ) :
    equivOfModuleEquivalence (e.trans d) =
      (equivOfModuleEquivalence e).trans (equivOfModuleEquivalence d) := by
  apply AddEquiv.toAddMonoidHom_injective
  apply K0.hom_ext_ofClass R
  intro a
  simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply,
    equivOfModuleEquivalence_ofClass, ProjectiveClass.equivOfModuleEquivalence_trans e d]

/-- Naturally isomorphic module-category functors induce the same K₀ map. -/
theorem equivOfModuleEquivalence_congr
    (e' : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)
    (α : e.functor ≅ e'.functor) :
    equivOfModuleEquivalence e = equivOfModuleEquivalence e' := by
  apply AddEquiv.toAddMonoidHom_injective
  apply K0.hom_ext_ofClass R
  intro a
  simp only [AddEquiv.coe_toAddMonoidHom, equivOfModuleEquivalence_ofClass,
    ProjectiveClass.equivOfModuleEquivalence_congr e e' α]

end K0

end KTheory
