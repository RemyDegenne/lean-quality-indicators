/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.Soberification
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The sober reflection of topological spaces

The full subcategory of `T₀` quasi-sober spaces is reflective in `TopCat`. The reflector
takes a space to its irreducible closed subsets with the topology of open intersections.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.1(b), Proposition 2.1.3, for the sober reflection.
- Mathlib, `Topology.Sober` and `CategoryTheory.Adjunction.Basic`, for
  irreducible closed subsets and the categorical adjunction interface.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace.IrreducibleCloseds

namespace TopologicalSpace

/-- The property of being both quasi-sober and `T₀`. -/
def soberProperty : CategoryTheory.ObjectProperty TopCat.{u} :=
  fun X => T0Space X ∧ QuasiSober X

/-- The full subcategory of sober topological spaces. -/
abbrev SoberTopCat : Type (u + 1) :=
  (soberProperty.{u}).FullSubcategory

/-- The canonical inclusion of sober spaces into topological spaces. -/
def soberInclusion : SoberTopCat.{u} ⥤ TopCat.{u} :=
  (soberProperty.{u}).ι

/-- The soberification functor on topological spaces. -/
def soberification : TopCat.{u} ⥤ SoberTopCat.{u} where
  obj X := ⟨TopCat.of (IrreducibleCloseds X), ⟨inferInstance, inferInstance⟩⟩
  map {X Y} f := ObjectProperty.homMk
    (TopCat.ofHom ⟨IrreducibleCloseds.map f.hom f.hom.continuous,
      IrreducibleCloseds.continuous_map f.hom⟩)
  map_id := by
    intro X
    apply ObjectProperty.hom_ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro F
    exact IrreducibleCloseds.map_id F
  map_comp := by
    intro X Y Z f g
    apply ObjectProperty.hom_ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro F
    exact IrreducibleCloseds.map_comp f.hom g.hom F

@[simp]
theorem soberification_map_apply {X Y : TopCat.{u}} (f : X ⟶ Y)
    (F : IrreducibleCloseds X) :
    (soberification.map f).hom.hom F = IrreducibleCloseds.map f.hom f.hom.continuous F :=
  rfl

/-- A map out of the soberification is equivalent to a map from the original space
into the included sober space, by restriction along the unit. -/
noncomputable def soberificationHomEquiv (X : TopCat.{u}) (Y : SoberTopCat.{u}) :
    (soberification.obj X ⟶ Y) ≃ (X ⟶ soberInclusion.obj Y) := by
  letI : T0Space Y.obj := Y.property.1
  letI : QuasiSober Y.obj := Y.property.2
  exact {
    toFun := fun h => TopCat.ofHom (h.hom.hom.comp (IrreducibleCloseds.unit X))
    invFun := fun f => ObjectProperty.homMk (TopCat.ofHom
      (IrreducibleCloseds.extend f.hom))
    left_inv := by
      intro h
      apply ObjectProperty.hom_ext
      apply TopCat.hom_ext
      exact (IrreducibleCloseds.extend_unique (Y := Y.obj) _ h.hom.hom rfl).symm
    right_inv := by
      intro f
      apply TopCat.hom_ext
      exact @IrreducibleCloseds.extend_comp_unit X Y.obj _ _ Y.property.2 Y.property.1 f.hom }

@[simp]
theorem soberificationHomEquiv_apply (X : TopCat.{u}) (Y : SoberTopCat.{u})
    (h : soberification.obj X ⟶ Y) :
    (soberificationHomEquiv X Y h).hom =
      h.hom.hom.comp (IrreducibleCloseds.unit X) :=
  rfl

@[simp]
theorem soberificationHomEquiv_symm_apply (X : TopCat.{u}) (Y : SoberTopCat.{u})
    (f : X ⟶ soberInclusion.obj Y) :
    ((soberificationHomEquiv X Y).symm f).hom.hom =
      @IrreducibleCloseds.extend X Y.obj _ _ Y.property.2 Y.property.1 f.hom :=
  rfl

/-- Soberification is left adjoint to inclusion of sober spaces;
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Proposition 2.1.3.
The proof uses the open-set characterization of the irreducible-closed topology. -/
noncomputable def soberificationAdjunction : soberification.{u} ⊣ soberInclusion :=
  Adjunction.mkOfHomEquiv {
    homEquiv := soberificationHomEquiv
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      let : T0Space Y.obj := Y.property.1
      let : QuasiSober Y.obj := Y.property.2
      apply ObjectProperty.hom_ext
      apply TopCat.hom_ext
      apply IrreducibleCloseds.continuous_ext_of_comp_unit (Y := Y.obj)
      apply ContinuousMap.ext
      intro x
      change (@IrreducibleCloseds.extend X' Y.obj _ _ Y.property.2 Y.property.1
          (g.hom.comp f.hom)).toFun
          (IrreducibleCloseds.unit X' x) =
        (@IrreducibleCloseds.extend X Y.obj _ _ Y.property.2 Y.property.1 g.hom).toFun
          (IrreducibleCloseds.map f.hom f.hom.continuous (IrreducibleCloseds.unit X' x))
      rw [IrreducibleCloseds.map_unit]
      have hleft := congrArg (fun k : C(X', Y.obj) => k x)
        (@IrreducibleCloseds.extend_comp_unit X' Y.obj _ _ Y.property.2 Y.property.1
          (g.hom.comp f.hom))
      have hright := congrArg (fun k : C(X, Y.obj) => k (f.hom x))
        (@IrreducibleCloseds.extend_comp_unit X Y.obj _ _ Y.property.2 Y.property.1 g.hom)
      exact hleft.trans hright.symm
    homEquiv_naturality_right := by
      intro X Y Y' f g
      apply TopCat.hom_ext
      rfl }

@[simp]
theorem soberificationAdjunction_unit_app (X : TopCat.{u}) :
    (soberificationAdjunction.unit.app X).hom = IrreducibleCloseds.unit X := by
  rfl

end TopologicalSpace
