/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.InverseImage
public import RingedSpaces.Modules.SheafInverseImageHom

set_option warningAsError true

/-!
# Pushforward of modules through a ringed-space morphism

The actual continuous inverse-image adjunction unit, followed by scalar restriction
along the inverse-image coefficient map, agrees with the complete structure map of
the original ringed-space morphism after forgetting commutativity. Consequently
the two corresponding pushforwards of module sheaves are naturally isomorphic.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), Definition 7.2.1 (p. 204) and Exercise 7.2.D(c,e) (p. 205):
  full-morphism pushforward and adjunction are requested there. The whole
  structure-sheaf map supplies coefficients; agreement with the Mathlib
  pushforward through the inverse-image adjunction is a project proof.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace RingedSpaces.Modules.RingedSpacePushforward

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The structure sheaf considered as a sheaf of ordinary rings. -/
abbrev ringSheaf (X : AlgebraicGeometry.RingedSpace.{u, u}) :
    X.carrier.Sheaf RingCat.{u} :=
  (SheafInverseImage.sheafForget X.carrier).obj X.sheaf

/-- The inverse-image coefficient map for the original full ringed-space morphism. -/
noncomputable def ringSheafMap :
    SheafInverseImage.targetRing f.hom.base Y.sheaf ⟶ ringSheaf X :=
  (SheafInverseImage.sheafForget X.carrier).map
    (AlgebraicGeometry.RingedSpace.inverseImageMap f)

/-- The original full structure map, forgotten from commutative rings to rings. -/
noncomputable def structureMap :
    ringSheaf Y ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (ringSheaf X) :=
  (SheafInverseImage.sheafForget Y.carrier).map
    ((CategoryTheory.Sheaf.homEquiv (X := Y.sheaf)
      (Y := (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf)).symm
        f.hom.c)

/-- Native pushforward of module sheaves through the original full morphism.
Vakil's *The Rising Sea* (21 October 2025 draft), Exercise 7.2.D(c)
(p. 205), requests the full-morphism functor; the construction uses
Mathlib's module-sheaf pushforward and the complete structure map. -/
noncomputable def pushforwardFunctor :
    SheafOfModules.{u} (ringSheaf X) ⥤ SheafOfModules.{u} (ringSheaf Y) :=
  SheafOfModules.pushforward (structureMap f)

set_option backward.isDefEq.respectTransparency false

/-- The complete forgotten mate identity, including the induced ring operations. -/
theorem actualUnit_comp_ringSheafMap :
    SheafInverseImage.actualUnit f.hom.base Y.sheaf ≫
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).map (ringSheafMap f) =
    structureMap f := by
  have identity := congrArg
    (fun t => (SheafInverseImage.sheafForget Y.carrier).map t)
    (AlgebraicGeometry.RingedSpace.inverseImageMap_unit f)
  simp only [Functor.map_comp, SheafInverseImage.pushforwardForget_map] at identity
  exact identity

/-- Scalar restriction then continuous pushforward equals native full-morphism pushforward. -/
noncomputable def restrictPushforwardIso :
    SheafOfModules.restrictScalars (ringSheafMap f) ⋙
      SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf ≅
    pushforwardFunctor f :=
  SheafOfModules.pushforwardComp (F := Opens.map f.hom.base)
      (G := 𝟭 (Opens X.carrier)) (K' := Opens.grothendieckTopology X.carrier)
      (R' := ringSheaf X)
      (SheafInverseImage.actualUnit f.hom.base Y.sheaf) (ringSheafMap f) ≪≫
    SheafOfModules.pushforwardCongr (actualUnit_comp_ringSheafMap f)

/-- On every target open, the original forgotten structure map acts as the
complete unit followed by the pushed-forward inverse-image coefficient map. -/
theorem structureMap_apply (U : (Opens Y.carrier)ᵒᵖ)
    (r : (ringSheaf Y).obj.obj U) :
    (structureMap f).hom.app U r =
      ((ringSheafMap f).hom.app ((Opens.map f.hom.base).op.obj U))
        ((SheafInverseImage.actualUnit f.hom.base Y.sheaf).hom.app U r) := by
  have equality := congrArg (fun t => t.hom.app U r) (actualUnit_comp_ringSheafMap f)
  exact equality.symm

/-- On each target open the forgotten ring map acts exactly as the original
commutative-ring structure map of the full morphism. -/
theorem structureMap_original (U : (Opens Y.carrier)ᵒᵖ)
    (r : Y.sheaf.obj.obj U) :
    (structureMap f).hom.app U r = f.hom.c.app U r := by
  have equality :=
    (CategoryTheory.Sheaf.homEquiv (X := Y.sheaf)
      (Y := (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf)).apply_symm_apply
        f.hom.c
  exact congrArg (fun t => t.app U r) equality

/-- The forward comparison is the identity on underlying sections at every open. -/
theorem restrictPushforwardIso_hom_app (M : SheafOfModules.{u} (ringSheaf X))
    (U : (Opens Y.carrier)ᵒᵖ)
    (m : ((SheafOfModules.restrictScalars (ringSheafMap f) ⋙
      SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf).obj M).val.obj U) :
    ((restrictPushforwardIso f).hom.app M).val.app U m = m := rfl

/-- The inverse comparison is likewise the identity on underlying sections. -/
theorem restrictPushforwardIso_inv_app (M : SheafOfModules.{u} (ringSheaf X))
    (U : (Opens Y.carrier)ᵒᵖ)
    (m : ((pushforwardFunctor f).obj M).val.obj U) :
    ((restrictPushforwardIso f).inv.app M).val.app U m = m := rfl

/-- On every target open, the forward comparison is linear for the original
full structure map, which defines the target module action. -/
theorem restrictPushforwardIso_smul (M : SheafOfModules.{u} (ringSheaf X))
    (U : (Opens Y.carrier)ᵒᵖ) (r : (ringSheaf Y).obj.obj U)
    (m : ((SheafOfModules.restrictScalars (ringSheafMap f) ⋙
      SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf).obj M).val.obj U) :
    ((restrictPushforwardIso f).hom.app M).val.app U (r • m) =
      r • ((restrictPushforwardIso f).hom.app M).val.app U m := by
  exact (((restrictPushforwardIso f).hom.app M).val.app U).hom.map_smul r m

/-- The inverse component is also linear for the original structure-map action. -/
theorem restrictPushforwardIso_inv_smul (M : SheafOfModules.{u} (ringSheaf X))
    (U : (Opens Y.carrier)ᵒᵖ) (r : (ringSheaf Y).obj.obj U)
    (m : ((pushforwardFunctor f).obj M).val.obj U) :
    ((restrictPushforwardIso f).inv.app M).val.app U (r • m) =
      r • ((restrictPushforwardIso f).inv.app M).val.app U m := by
  exact (((restrictPushforwardIso f).inv.app M).val.app U).hom.map_smul r m

/-- The forward comparison is natural in morphisms of module sheaves. -/
theorem restrictPushforwardIso_naturality {M N : SheafOfModules.{u} (ringSheaf X)}
    (h : M ⟶ N) :
    (SheafOfModules.restrictScalars (ringSheafMap f) ⋙
      SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf).map h ≫
        (restrictPushforwardIso f).hom.app N =
      (restrictPushforwardIso f).hom.app M ≫ (pushforwardFunctor f).map h :=
  (restrictPushforwardIso f).hom.naturality h

/-- Naturality evaluated on a section of an arbitrary target open. -/
theorem restrictPushforwardIso_naturality_apply
    {M N : SheafOfModules.{u} (ringSheaf X)} (h : M ⟶ N)
    (U : (Opens Y.carrier)ᵒᵖ)
    (m : ((SheafOfModules.restrictScalars (ringSheafMap f) ⋙
      SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf).obj M).val.obj U) :
    ((restrictPushforwardIso f).hom.app N).val.app U
      (((SheafOfModules.restrictScalars (ringSheafMap f) ⋙
        SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf).map h).val.app U m) =
    ((pushforwardFunctor f).map h).val.app U
      (((restrictPushforwardIso f).hom.app M).val.app U m) := by
  exact congrArg (fun t => t.val.app U m) (restrictPushforwardIso_naturality f h)

/-- Both inverse laws hold as equalities of module-sheaf morphisms. -/
theorem restrictPushforwardIso_inverseLaws (M : SheafOfModules.{u} (ringSheaf X)) :
    (restrictPushforwardIso f).hom.app M ≫ (restrictPushforwardIso f).inv.app M =
        𝟙 _ ∧
      (restrictPushforwardIso f).inv.app M ≫ (restrictPushforwardIso f).hom.app M =
        𝟙 _ :=
  ⟨(restrictPushforwardIso f).hom_inv_id_app M,
    (restrictPushforwardIso f).inv_hom_id_app M⟩

end RingedSpaces.Modules.RingedSpacePushforward

#lint
