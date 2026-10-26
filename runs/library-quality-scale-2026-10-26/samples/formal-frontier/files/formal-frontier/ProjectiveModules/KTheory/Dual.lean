/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Dual.ModuleCat
public import ProjectiveModules.KTheory.ScalarExtension
public import ProjectiveModules.Module.RightRegular
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

import ProjectiveModules.Module.Bidual
import Mathlib.LinearAlgebra.Prod

/-!
# Opposite-ring duality on projective classes and K₀

For an arbitrary ring `R`, right-module duality induces additive equivalences
`ProjectiveClass.dualEquiv R` and `K0.dualEquiv R` with the corresponding
objects for `Rᵐᵒᵖ`. A right `R`-module is an `Rᵐᵒᵖ`-module. Its ordinary-carrier
dual `M →ₗ[Rᵐᵒᵖ] R` is a left `R`-module, not yet a right `Rᵐᵒᵖ`-module.
We use the canonical bundled restriction of scalars along
`(RingEquiv.opOp R).symm.toRingHom` to obtain that right-module convention.

The class map descends duals of finite-projective reference modules through
`ProjectiveClass.lift`. Addition is binary direct sum, modeled by products,
not tensor product. The inverse dualizes over `Rᵐᵒᵖ` and then applies the
existing class map along the inverse double-opposite ring isomorphism.
Twice dualizing therefore equals scalar extension along `RingEquiv.opOp R`,
rather than a literal identity between classes over different rings.

The K₀ equivalence is the additive localization of the class equivalence.
Both completion squares and universal-extension characterizations are stated
as equalities of whole homomorphisms. The module formulas allow independent
scalar and carrier universes; a dual carrier has their maximum. No
commutativity, nontriviality, freeness, smallness or cancellation is assumed.
Duality is used on finite projective modules, not as an ordinary equivalence
of whole module categories.

## References and credits

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II:
  finite-projective right modules, opposite rings and the group completion K₀.
* Projective Modules' ordinary-carrier right dual, finite-projective Hom and
  bidual comparisons, finite-projective representatives, class descent and
  scalar-extension maps.
* Mathlib's opposite-ring and module conventions, bundled restriction of
  scalars and additive localization; Alex J. Best and Yaël Dillies'
  Grothendieck-group formalization.
-/

@[expose] public section

universe u w w'

open CategoryTheory

namespace KTheory

variable (R : Type u) [Ring R]

private noncomputable abbrev normalizedRightDual (M : ModuleCat.{w} Rᵐᵒᵖ) :
    ModuleCat.{max u w} Rᵐᵒᵖᵐᵒᵖ :=
  (ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).obj
    ((ModuleCat.rightDual R).obj (Opposite.op M))

namespace ProjectiveClass

private noncomputable def normalizedRightDualFP
    (X : ModuleCat.FiniteProjective.{u, w} Rᵐᵒᵖ) :
    ModuleCat.FiniteProjective.{u, max u w} Rᵐᵒᵖᵐᵒᵖ :=
  ⟨normalizedRightDual R X.obj,
    ModuleCat.isFiniteProjective_rightDual_restrictScalars R X.obj X.property⟩

private noncomputable def normalizedRightDualCongr
    {M : ModuleCat.{w} Rᵐᵒᵖ} {N : ModuleCat.{w'} Rᵐᵒᵖ}
    (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    normalizedRightDual R M ≃ₗ[Rᵐᵒᵖᵐᵒᵖ] normalizedRightDual R N :=
  (ModuleCat.rightDualRestrictScalarsEquiv R M).trans
    ((LinearEquiv.congrLeft Rᵐᵒᵖ Rᵐᵒᵖᵐᵒᵖ e).trans
      (ModuleCat.rightDualRestrictScalarsEquiv R N).symm)

private noncomputable def canonicalDualClassValue
    (X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) : ProjectiveClass Rᵐᵒᵖ :=
  @ProjectiveClass.of Rᵐᵒᵖ _ (normalizedRightDual R X.obj) _ _
    (ModuleCat.isFiniteProjective_rightDual_restrictScalars R X.obj X.property).1
    (ModuleCat.isFiniteProjective_rightDual_restrictScalars R X.obj X.property).2

private theorem canonicalDualClassValue_iso
    {X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ} (i : X ≅ Y) :
    canonicalDualClassValue R X = canonicalDualClassValue R Y := by
  exact of_eq_of_equiv Rᵐᵒᵖ (normalizedRightDualFP R X)
    (N := normalizedRightDualFP R Y)
    (normalizedRightDualCongr R (ModuleCat.FiniteProjective.isoToLinearEquiv i))

private theorem canonicalDualClassValue_zero :
    canonicalDualClassValue R
      (ModuleCat.FiniteProjective.of Rᵐᵒᵖ PUnit.{u + 1}) = 0 := by
  let : Subsingleton (normalizedRightDual R (ModuleCat.of Rᵐᵒᵖ PUnit.{u + 1})) :=
    show Subsingleton (PUnit.{u + 1} →ₗ[Rᵐᵒᵖ] R) from inferInstance
  exact of_zero Rᵐᵒᵖ
    (normalizedRightDual R (ModuleCat.of Rᵐᵒᵖ PUnit.{u + 1}))

private theorem canonicalDualClassValue_add
    (X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
    canonicalDualClassValue R (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) =
      canonicalDualClassValue R X + canonicalDualClassValue R Y := by
  let DX := normalizedRightDualFP R X
  let DY := normalizedRightDualFP R Y
  let DXY := normalizedRightDualFP R
    (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y))
  let p : ((X × Y) →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖᵐᵒᵖ]
      ((X →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) × (Y →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ)) :=
    (LinearMap.coprodEquiv Rᵐᵒᵖᵐᵒᵖ).symm
  let e : DXY ≃ₗ[Rᵐᵒᵖᵐᵒᵖ] (DX × DY) :=
    (ModuleCat.rightDualRestrictScalarsEquiv R
      (ModuleCat.of Rᵐᵒᵖ (X × Y))).trans
      (p.trans ((ModuleCat.rightDualRestrictScalarsEquiv R X.obj).symm.prodCongr
        (ModuleCat.rightDualRestrictScalarsEquiv R Y.obj).symm))
  exact (of_eq_of_equiv Rᵐᵒᵖ DXY e).trans (of_prod Rᵐᵒᵖ DX DY)

private noncomputable def canonicalDualClassHom :
    ProjectiveClass R →+ ProjectiveClass Rᵐᵒᵖ :=
  ProjectiveClass.lift R (canonicalDualClassValue R)
    (canonicalDualClassValue_iso R) (canonicalDualClassValue_zero R)
    (canonicalDualClassValue_add R)

private theorem canonicalDualClassHom_of
    (X : ModuleCat.FiniteProjective.{u, w} Rᵐᵒᵖ) :
    canonicalDualClassHom R (of R X) = of Rᵐᵒᵖ (normalizedRightDualFP R X) := by
  calc
    canonicalDualClassHom R (of R X) =
        canonicalDualClassValue R (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ X) :=
      lift_of_module (R := R) (M := X) (f := canonicalDualClassValue R)
        (hiso := canonicalDualClassValue_iso R) (hzero := canonicalDualClassValue_zero R)
        (hadd := canonicalDualClassValue_add R)
    _ = of Rᵐᵒᵖ (normalizedRightDualFP R X) :=
      of_eq_of_equiv Rᵐᵒᵖ
        (normalizedRightDualFP R (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ X))
        (N := normalizedRightDualFP R X)
        (normalizedRightDualCongr R (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ X))

-- The bidual comparison still takes values in Rᵐᵒᵖ. Only its outer scalar
-- action changes in the second normalization; it is not an R-valued pairing.
private noncomputable def doubleDualExtensionEquiv
    (X : ModuleCat.FiniteProjective.{u, w} Rᵐᵒᵖ) :
    ModuleCat.RightExtension.Obj (RingEquiv.opOp R).toRingHom X ≃ₗ[Rᵐᵒᵖᵐᵒᵖᵐᵒᵖ]
      normalizedRightDual Rᵐᵒᵖ (normalizedRightDual R X.obj) := by
  let D := normalizedRightDual R X.obj
  let b : X ≃ₗ[Rᵐᵒᵖ] (D →ₗ[Rᵐᵒᵖᵐᵒᵖ] Rᵐᵒᵖ) :=
    (LinearMap.bidualEvalEquiv Rᵐᵒᵖ X).trans
      (LinearEquiv.congrLeft Rᵐᵒᵖ Rᵐᵒᵖ
        (ModuleCat.rightDualRestrictScalarsEquiv R X.obj).symm)
  let f : X →ₛₗ[RingHom.op (RingEquiv.opOp R).toRingHom]
      normalizedRightDual Rᵐᵒᵖ D :=
    { toFun := b
      map_add' := b.map_add
      map_smul' := fun r x => by
        change b (r • x) = r • b x
        exact b.map_smul r x }
  let g := ModuleCat.RightExtension.fromSemilinear (RingEquiv.opOp R).toRingHom f
  have hg (x : X) :
      g (ModuleCat.RightExtension.tmulOne (RingEquiv.opOp R).toRingHom x) = b x := by
    change ModuleCat.RightExtension.fromSemilinear (RingEquiv.opOp R).toRingHom f
      (ModuleCat.RightExtension.tmul (RingEquiv.opOp R).toRingHom x 1) = f x
    rw [ModuleCat.RightExtension.fromSemilinear_tmul]
    exact one_smul Rᵐᵒᵖᵐᵒᵖᵐᵒᵖ (f x)
  refine LinearEquiv.ofBijective g ⟨?_, ?_⟩
  · intro z z' h
    obtain ⟨x, rfl⟩ := ModuleCat.RightExtension.tmulOne_surjective
      (RingEquiv.opOp R).toRingHom (RingEquiv.opOp R).surjective z
    obtain ⟨x', rfl⟩ := ModuleCat.RightExtension.tmulOne_surjective
      (RingEquiv.opOp R).toRingHom (RingEquiv.opOp R).surjective z'
    exact congrArg (ModuleCat.RightExtension.tmulOne (RingEquiv.opOp R).toRingHom)
      (b.injective ((hg x).symm.trans (h.trans (hg x'))))
  · intro y
    obtain ⟨x, hx⟩ := b.surjective y
    exact ⟨ModuleCat.RightExtension.tmulOne (RingEquiv.opOp R).toRingHom x,
      (hg x).trans hx⟩

private theorem canonicalDualClassHom_comp :
    (canonicalDualClassHom Rᵐᵒᵖ).comp (canonicalDualClassHom R) =
      map (RingEquiv.opOp R).toRingHom := by
  apply addHom_ext R
  intro X
  let D := normalizedRightDualFP R X
  let DD := normalizedRightDualFP Rᵐᵒᵖ D
  change canonicalDualClassHom Rᵐᵒᵖ (canonicalDualClassHom R (of R X)) =
    map (RingEquiv.opOp R).toRingHom (of R X)
  rw [canonicalDualClassHom_of R X]
  change canonicalDualClassHom Rᵐᵒᵖ (of Rᵐᵒᵖ D) =
    map (RingEquiv.opOp R).toRingHom (of R X)
  rw [canonicalDualClassHom_of Rᵐᵒᵖ D, map_of]
  -- Use the bundled scalar action together with its finite-projective witnesses.
  exact (@of_eq_of_equiv Rᵐᵒᵖᵐᵒᵖ _
    (ModuleCat.RightExtension.Obj (RingEquiv.opOp R).toRingHom X) _ _
    (ModuleCat.RightExtension.instFinite (RingEquiv.opOp R).toRingHom)
    (ModuleCat.RightExtension.instProjective (RingEquiv.opOp R).toRingHom)
    DD DD.obj.isAddCommGroup DD.obj.isModule DD.property.1 DD.property.2
    (doubleDualExtensionEquiv R X)).symm

private theorem map_opOp_symm_comp :
    (map (RingEquiv.opOp R).symm.toRingHom).comp
        (map (RingEquiv.opOp R).toRingHom) = AddMonoidHom.id (ProjectiveClass R) := by
  rw [← map_comp, RingEquiv.symm_toRingHom_comp_toRingHom, map_id]

private theorem map_opOp_comp_symm :
    (map (RingEquiv.opOp R).toRingHom).comp
        (map (RingEquiv.opOp R).symm.toRingHom) =
      AddMonoidHom.id (ProjectiveClass Rᵐᵒᵖᵐᵒᵖ) := by
  rw [← map_comp, RingEquiv.toRingHom_comp_symm_toRingHom, map_id]

private theorem canonicalDualClassHom_leftInverse :
    Function.LeftInverse
      ((map (RingEquiv.opOp R).symm.toRingHom).comp (canonicalDualClassHom Rᵐᵒᵖ))
      (canonicalDualClassHom R) := by
  intro a
  change map (RingEquiv.opOp R).symm.toRingHom
    (canonicalDualClassHom Rᵐᵒᵖ (canonicalDualClassHom R a)) = a
  have h := DFunLike.congr_fun (canonicalDualClassHom_comp R) a
  change canonicalDualClassHom Rᵐᵒᵖ (canonicalDualClassHom R a) =
    map (RingEquiv.opOp R).toRingHom a at h
  rw [h]
  exact DFunLike.congr_fun (map_opOp_symm_comp R) a

private theorem canonicalDualClassHom_injective :
    Function.Injective (canonicalDualClassHom R) :=
  (canonicalDualClassHom_leftInverse R).injective

/-- Right-module duality gives the opposite-ring equivalence of finite-projective
class monoids. The inverse dualizes over the opposite ring and transports back
along the inverse double-opposite ring isomorphism, as in Weibel's *The K-book*,
Chapter II. -/
@[no_expose] noncomputable def dualEquiv :
    ProjectiveClass R ≃+ ProjectiveClass Rᵐᵒᵖ where
  toFun := canonicalDualClassHom R
  invFun := (ProjectiveClass.map (RingEquiv.opOp R).symm.toRingHom).comp
    (canonicalDualClassHom Rᵐᵒᵖ)
  left_inv := canonicalDualClassHom_leftInverse R
  right_inv := by
    intro y
    apply canonicalDualClassHom_injective Rᵐᵒᵖ
    change canonicalDualClassHom Rᵐᵒᵖ
      (canonicalDualClassHom R
        (map (RingEquiv.opOp R).symm.toRingHom (canonicalDualClassHom Rᵐᵒᵖ y))) =
      canonicalDualClassHom Rᵐᵒᵖ y
    have h := DFunLike.congr_fun (canonicalDualClassHom_comp R)
      (map (RingEquiv.opOp R).symm.toRingHom (canonicalDualClassHom Rᵐᵒᵖ y))
    exact h.trans
      (DFunLike.congr_fun (map_opOp_comp_symm R) (canonicalDualClassHom Rᵐᵒᵖ y))
  map_add' := (canonicalDualClassHom R).map_add

/-- On a finite projective right module in any carrier universe, duality takes
the class of its ordinary-carrier dual with the canonical double-opposite
restriction of scalars. -/
theorem dualEquiv_of_module (M : Type w)
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    dualEquiv R (ProjectiveClass.of R M) =
      @ProjectiveClass.of Rᵐᵒᵖ _
        ((ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).obj
          ((ModuleCat.rightDual R).obj (Opposite.op (ModuleCat.of Rᵐᵒᵖ M)))) _ _
        (ModuleCat.isFiniteProjective_rightDual_restrictScalars R
          (ModuleCat.of Rᵐᵒᵖ M) ⟨inferInstance, inferInstance⟩).1
        (ModuleCat.isFiniteProjective_rightDual_restrictScalars R
          (ModuleCat.of Rᵐᵒᵖ M) ⟨inferInstance, inferInstance⟩).2 := by
  exact canonicalDualClassHom_of R (ModuleCat.FiniteProjective.of Rᵐᵒᵖ M)

/-- Inverse evaluation on an arbitrary-height right `Rᵐᵒᵖ`-module first takes
its normalized dual over `Rᵐᵒᵖ`, then uses the existing scalar-extension class
map to return from the double opposite to `R`. -/
theorem dualEquiv_symm_of_module (N : Type w')
    [AddCommGroup N] [Module Rᵐᵒᵖᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖᵐᵒᵖ N] :
    (dualEquiv R).symm (ProjectiveClass.of Rᵐᵒᵖ N) =
      ProjectiveClass.map (RingEquiv.opOp R).symm.toRingHom
        (@ProjectiveClass.of Rᵐᵒᵖᵐᵒᵖ _
          ((ModuleCat.restrictScalars (RingEquiv.opOp Rᵐᵒᵖ).symm.toRingHom).obj
            ((ModuleCat.rightDual Rᵐᵒᵖ).obj
              (Opposite.op (ModuleCat.of Rᵐᵒᵖᵐᵒᵖ N)))) _ _
          (ModuleCat.isFiniteProjective_rightDual_restrictScalars Rᵐᵒᵖ
            (ModuleCat.of Rᵐᵒᵖᵐᵒᵖ N) ⟨inferInstance, inferInstance⟩).1
          (ModuleCat.isFiniteProjective_rightDual_restrictScalars Rᵐᵒᵖ
            (ModuleCat.of Rᵐᵒᵖᵐᵒᵖ N) ⟨inferInstance, inferInstance⟩).2) := by
  exact congrArg (map (RingEquiv.opOp R).symm.toRingHom)
    (canonicalDualClassHom_of Rᵐᵒᵖ
      (ModuleCat.FiniteProjective.of Rᵐᵒᵖᵐᵒᵖ N))

/-- Duality sends the ordinary-carrier right regular module to the
ordinary-carrier right regular module of the opposite ring. -/
theorem dualEquiv_regular :
    dualEquiv R (ProjectiveClass.of R R) =
      ProjectiveClass.of Rᵐᵒᵖ Rᵐᵒᵖ := by
  let X := ModuleCat.FiniteProjective.of Rᵐᵒᵖ R
  let D := normalizedRightDualFP R X
  let e : D ≃ₗ[Rᵐᵒᵖᵐᵒᵖ] Rᵐᵒᵖ :=
    (ModuleCat.rightDualRestrictScalarsEquiv R (ModuleCat.of Rᵐᵒᵖ R)).trans
      ((LinearEquiv.congrLeft Rᵐᵒᵖ Rᵐᵒᵖᵐᵒᵖ
        (MulOpposite.opLinearEquiv Rᵐᵒᵖ)).trans
          (LinearMap.ringLmapEquivSelf Rᵐᵒᵖ Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ))
  exact (canonicalDualClassHom_of R X).trans (of_eq_of_equiv Rᵐᵒᵖ D e)

/-- The whole twice-dual class homomorphism is scalar extension along the
canonical double-opposite ring isomorphism, not an identity across rings. -/
theorem dualEquiv_comp_dualEquiv :
    (dualEquiv Rᵐᵒᵖ).toAddMonoidHom.comp (dualEquiv R).toAddMonoidHom =
      ProjectiveClass.map (RingEquiv.opOp R).toRingHom := by
  exact canonicalDualClassHom_comp R

end ProjectiveClass

namespace K0

/-- The opposite-ring additive equivalence on K₀ obtained by localizing the
finite-projective class duality. This is the group-completion duality of
Weibel's *The K-book*, Chapter II. -/
noncomputable def dualEquiv : K0 R ≃+ K0 Rᵐᵒᵖ :=
  (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R))).addEquivOfAddEquiv
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass Rᵐᵒᵖ)))
    (j := ProjectiveClass.dualEquiv R) (by
      rw [← AddMonoidHom.mrange_eq_map]
      exact AddMonoidHom.mrange_eq_top_of_surjective _
        (ProjectiveClass.dualEquiv R).surjective)

/-- The whole forward completion square intertwines class and K₀ duality. -/
theorem dualEquiv_comp_ofClass :
    (dualEquiv R).toAddMonoidHom.comp (K0.ofClass R) =
      (K0.ofClass Rᵐᵒᵖ).comp (ProjectiveClass.dualEquiv R).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro a
  exact AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R)))
    (k := AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass Rᵐᵒᵖ)))
    (j := ProjectiveClass.dualEquiv R) (by
      rw [← AddMonoidHom.mrange_eq_map]
      exact AddMonoidHom.mrange_eq_top_of_surjective _
        (ProjectiveClass.dualEquiv R).surjective) a

/-- The whole forward K₀ homomorphism is the universal extension of class
duality followed by the opposite-ring completion map. -/
theorem dualEquiv_toAddMonoidHom_eq_lift :
    (dualEquiv R).toAddMonoidHom =
      K0.lift R ((K0.ofClass Rᵐᵒᵖ).comp
        (ProjectiveClass.dualEquiv R).toAddMonoidHom) := by
  apply K0.hom_ext_ofClass R
  intro a
  simpa only [K0.lift_ofClass, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] using
    DFunLike.congr_fun (dualEquiv_comp_ofClass R) a

/-- The whole inverse completion square uses the inverse class equivalence. -/
theorem dualEquiv_symm_comp_ofClass :
    (dualEquiv R).symm.toAddMonoidHom.comp (K0.ofClass Rᵐᵒᵖ) =
      (K0.ofClass R).comp (ProjectiveClass.dualEquiv R).symm.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro a
  let source := AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R))
  let target := AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass Rᵐᵒᵖ))
  have htop : (⊤ : AddSubmonoid (ProjectiveClass R)).map
      (ProjectiveClass.dualEquiv R).toAddMonoidHom = ⊤ := by
    rw [← AddMonoidHom.mrange_eq_map]
    exact AddMonoidHom.mrange_eq_top_of_surjective _
      (ProjectiveClass.dualEquiv R).surjective
  -- The inverse is the stock lift from the target localization with changed domain.
  change (source.addEquivOfLocalizations
    (target.ofAddEquivOfDom (k := ProjectiveClass.dualEquiv R) htop)).symm
      (target a) = source ((ProjectiveClass.dualEquiv R).symm a)
  rw [AddSubmonoid.LocalizationMap.addEquivOfLocalizations_symm_apply,
    ← target.ofAddEquivOfDom_comp_symm (k := ProjectiveClass.dualEquiv R) htop a]
  exact (target.ofAddEquivOfDom htop).lift_eq source.map_addUnits _

/-- The whole inverse K₀ homomorphism is the universal extension of the
inverse class equivalence followed by completion over `R`. -/
theorem dualEquiv_symm_toAddMonoidHom_eq_lift :
    (dualEquiv R).symm.toAddMonoidHom =
      K0.lift Rᵐᵒᵖ ((K0.ofClass R).comp
        (ProjectiveClass.dualEquiv R).symm.toAddMonoidHom) := by
  apply K0.hom_ext_ofClass Rᵐᵒᵖ
  intro a
  simpa only [K0.lift_ofClass, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] using
    DFunLike.congr_fun (dualEquiv_symm_comp_ofClass R) a

/-- Duality evaluates on a finite-projective K₀ generator in any carrier
universe using the canonical bundled normalized dual. -/
theorem dualEquiv_of_module (M : Type w)
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    dualEquiv R (K0.of R M) =
      @K0.of Rᵐᵒᵖ _
        ((ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).obj
          ((ModuleCat.rightDual R).obj (Opposite.op (ModuleCat.of Rᵐᵒᵖ M)))) _ _
        (ModuleCat.isFiniteProjective_rightDual_restrictScalars R
          (ModuleCat.of Rᵐᵒᵖ M) ⟨inferInstance, inferInstance⟩).1
        (ModuleCat.isFiniteProjective_rightDual_restrictScalars R
          (ModuleCat.of Rᵐᵒᵖ M) ⟨inferInstance, inferInstance⟩).2 := by
  simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ProjectiveClass.dualEquiv_of_module, K0.ofClass_of] using
    DFunLike.congr_fun (dualEquiv_comp_ofClass R) (ProjectiveClass.of R M)

/-- Inverse K₀ generator evaluation dualizes over the opposite ring and then
uses the existing scalar-extension K₀ map along inverse double-opposite
transport. The target carrier height is arbitrary. -/
theorem dualEquiv_symm_of_module (N : Type w')
    [AddCommGroup N] [Module Rᵐᵒᵖᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖᵐᵒᵖ N] :
    (dualEquiv R).symm (K0.of Rᵐᵒᵖ N) =
      K0.map (RingEquiv.opOp R).symm.toRingHom
        (@K0.of Rᵐᵒᵖᵐᵒᵖ _
          ((ModuleCat.restrictScalars (RingEquiv.opOp Rᵐᵒᵖ).symm.toRingHom).obj
            ((ModuleCat.rightDual Rᵐᵒᵖ).obj
              (Opposite.op (ModuleCat.of Rᵐᵒᵖᵐᵒᵖ N)))) _ _
          (ModuleCat.isFiniteProjective_rightDual_restrictScalars Rᵐᵒᵖ
            (ModuleCat.of Rᵐᵒᵖᵐᵒᵖ N) ⟨inferInstance, inferInstance⟩).1
          (ModuleCat.isFiniteProjective_rightDual_restrictScalars Rᵐᵒᵖ
            (ModuleCat.of Rᵐᵒᵖᵐᵒᵖ N) ⟨inferInstance, inferInstance⟩).2) := by
  simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ProjectiveClass.dualEquiv_symm_of_module, ← K0.map_ofClass, K0.ofClass_of] using
    DFunLike.congr_fun (dualEquiv_symm_comp_ofClass R) (ProjectiveClass.of Rᵐᵒᵖ N)

/-- The ordinary right regular K₀ generator is normalized to that of the
opposite ring. -/
theorem dualEquiv_regular :
    dualEquiv R (K0.of R R) = K0.of Rᵐᵒᵖ Rᵐᵒᵖ := by
  simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ProjectiveClass.dualEquiv_regular, K0.ofClass_of] using
    DFunLike.congr_fun (dualEquiv_comp_ofClass R) (ProjectiveClass.of R R)

/-- The whole twice-dual K₀ homomorphism is the existing scalar-extension map
along the canonical double-opposite ring isomorphism. -/
theorem dualEquiv_comp_dualEquiv :
    (dualEquiv Rᵐᵒᵖ).toAddMonoidHom.comp (dualEquiv R).toAddMonoidHom =
      K0.map (RingEquiv.opOp R).toRingHom := by
  apply K0.hom_ext_ofClass R
  intro a
  have hR := DFunLike.congr_fun (dualEquiv_comp_ofClass R) a
  have hRop := DFunLike.congr_fun (dualEquiv_comp_ofClass Rᵐᵒᵖ)
    (ProjectiveClass.dualEquiv R a)
  have htwice := DFunLike.congr_fun (ProjectiveClass.dualEquiv_comp_dualEquiv R) a
  simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, K0.map_ofClass] using
    (congrArg (dualEquiv Rᵐᵒᵖ) hR).trans
      (hRop.trans (congrArg (K0.ofClass Rᵐᵒᵖᵐᵒᵖ) htwice))

end K0

end KTheory
