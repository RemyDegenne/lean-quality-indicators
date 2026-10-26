/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.GenericPointFunctionField
public import SchemeProperties.JacobsonBirationalObstruction
public import SchemeProperties.RationalMapPartialIso
public import SchemeProperties.IntegralDominantRationalCategoryOver

@[expose] public section

/-!
# Native rational inverses at a generic point

A dominant native rational map from a subsingleton scheme to a nontrivial Jacobson
scheme cannot have a dominant two-sided inverse. For an integral target, this
applies to the actual generic-point morphism over any chosen base, even though
its reversed function-field map is an isomorphism.
-/

set_option warningAsError true
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RationalMap

/-- Dominant native rational maps from a subsingleton scheme to a nontrivial
Jacobson scheme cannot have a dominant two-sided inverse. -/
theorem not_twoSidedInverse_of_subsingleton_of_jacobson {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [Subsingleton X] [JacobsonSpace Y] [Nontrivial Y]
    (forward : X ⤏ Y) (reverse : Y ⤏ X)
    [forward.IsDominant] [reverse.IsDominant] :
    ¬ (forward.comp reverse = RationalMap.id X ∧
      reverse.comp forward = RationalMap.id Y) := by
  rintro ⟨hforward, hreverse⟩
  obtain ⟨partialIso, _, _⟩ :=
    exists_partialIso_of_inverse forward reverse hforward hreverse
  exact Scheme.not_birational_of_subsingleton_of_jacobson ⟨partialIso⟩

end AlgebraicGeometry.Scheme.RationalMap

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) [IsIntegral Y]

/-- The actual dominant generic-point rational quotient, over a freely chosen
total target structure morphism. The source structure is induced by composition. -/
def genericPointRationalHom {S : Scheme.{u}} (sY : Y ⟶ S) :
    IntegralDominantRationalSchemeOver.of
        (Y.fromSpecStalk (genericPoint Y) ≫ sY) ⟶
      IntegralDominantRationalSchemeOver.of sY := by
  refine ⟨(Y.fromSpecStalk (genericPoint Y)).toRationalMap,
    fromSpecStalk_genericPoint_toRationalMap_isDominant Y, ?_⟩
  apply (IntegralDominantRationalSchemeOver.isOver_iff_compHom
    (S := S) (X := .of (Y.fromSpecStalk (genericPoint Y) ≫ sY))
    (Y := .of sY)
    (r := (Y.fromSpecStalk (genericPoint Y)).toRationalMap)).2
  change (Y.fromSpecStalk (genericPoint Y)).toRationalMap.compHom sY =
    (Y.fromSpecStalk (genericPoint Y) ≫ sY).toRationalMap
  rw [← RationalMap.compHom_toRationalMap, Hom.toPartialMap_compHom]

/-- The chosen-base arrow has the exact quotient of the canonical total map. -/
@[simp] theorem genericPointRationalHom_toRationalMap {S : Scheme.{u}} (sY : Y ⟶ S) :
    (genericPointRationalHom Y sY).toRationalMap =
      (Y.fromSpecStalk (genericPoint Y)).toRationalMap := rfl

/-- The generic-point chosen-base rational arrow is not invertible, although its
actual reversed function-field map is invertible. No finiteness or separatedness
hypothesis is imposed on either endpoint or the base. -/
theorem genericPointRationalHom_boundary {S : Scheme.{u}} (sY : Y ⟶ S)
    [JacobsonSpace Y] [Nontrivial Y] :
    IsIso (genericPointRationalHom Y sY).toRationalMap.functionFieldMap ∧
      ¬ IsIso (genericPointRationalHom Y sY) := by
  constructor
  · simpa only [genericPointRationalHom_toRationalMap,
      IntegralDominantRationalSchemeOver.of] using
      (inferInstance : IsIso
        (Y.fromSpecStalk (genericPoint Y)).toRationalMap.functionFieldMap)
  · intro hIso
    let forward := genericPointRationalHom Y sY
    haveI : IsIso forward := hIso
    haveI hsource : Subsingleton
        (IntegralDominantRationalSchemeOver.of
          (Y.fromSpecStalk (genericPoint Y) ≫ sY)).toScheme := by
      change Subsingleton (PrimeSpectrum Y.functionField)
      infer_instance
    haveI : JacobsonSpace (IntegralDominantRationalSchemeOver.of sY).toScheme := by
      change JacobsonSpace Y
      infer_instance
    haveI : Nontrivial (IntegralDominantRationalSchemeOver.of sY).toScheme := by
      change Nontrivial Y
      infer_instance
    have hforward : forward.toRationalMap.comp (inv forward).toRationalMap =
        RationalMap.id (Spec Y.functionField) := by
      have h := congrArg (fun arrow => arrow.toRationalMap) (IsIso.hom_inv_id forward)
      rw [IntegralDominantRationalSchemeOver.toRationalMap_comp,
        IntegralDominantRationalSchemeOver.toRationalMap_id] at h
      simpa only [IntegralDominantRationalSchemeOver.of] using h
    have hreverse : (inv forward).toRationalMap.comp forward.toRationalMap =
        RationalMap.id Y := by
      have h := congrArg (fun arrow => arrow.toRationalMap) (IsIso.inv_hom_id forward)
      rw [IntegralDominantRationalSchemeOver.toRationalMap_comp,
        IntegralDominantRationalSchemeOver.toRationalMap_id] at h
      simpa only [IntegralDominantRationalSchemeOver.of] using h
    exact RationalMap.not_twoSidedInverse_of_subsingleton_of_jacobson
      forward.toRationalMap (inv forward).toRationalMap ⟨hforward, hreverse⟩

end AlgebraicGeometry.Scheme
