/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# The category of finite projective modules

This file defines the full subcategory of `ModuleCat R` on the finitely
generated projective modules.  It proves closure under finite products and
equips the subcategory with finite biproducts.

The construction works over an arbitrary ring.  In particular, the category
of finite projective right `R`-modules is obtained by applying it to `Rᵐᵒᵖ`.
-/

@[expose] public section

universe uR uM

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

variable (R : Type uR) [Ring R]

/-- The property of a module being both finitely generated and projective. -/
def isFiniteProjective : ObjectProperty (ModuleCat.{uM} R) :=
  fun P ↦ Module.Finite R P ∧ Module.Projective R P

variable {R} in
lemma isFiniteProjective_iff (P : ModuleCat.{uM} R) :
    isFiniteProjective R P ↔ Module.Finite R P ∧ Module.Projective R P :=
  Iff.rfl

/-- The full subcategory of finitely generated projective `R`-modules. -/
abbrev FiniteProjective := (isFiniteProjective.{uR, uM} R).FullSubcategory

namespace FiniteProjective

variable {R} in
/-- The underlying type of a finite projective module. -/
@[reducible]
def carrier (M : FiniteProjective.{uR, uM} R) : Type uM := M.obj

instance : CoeSort (FiniteProjective.{uR, uM} R) (Type uM) :=
  ⟨carrier⟩

attribute [coe] carrier

@[simp]
theorem obj_carrier (M : FiniteProjective.{uR, uM} R) : M.obj.carrier = M.carrier := rfl

instance (M : FiniteProjective.{uR, uM} R) : Module.Finite R M :=
  M.property.1

instance (M : FiniteProjective.{uR, uM} R) : Module.Projective R M :=
  M.property.2

/-- Bundle an unbundled finite projective module. -/
abbrev of (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] : FiniteProjective R :=
  ⟨ModuleCat.of R M, ⟨inferInstance, inferInstance⟩⟩

@[simp]
theorem of_carrier (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    (of R M : Type uM) = M := rfl

/-- Bundle a linear map between finite projective modules. -/
abbrev ofHom {M N : Type uM} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) : of R M ⟶ of R N :=
  ConcreteCategory.ofHom f

/-- Two morphisms of finite projective modules are equal when their underlying
linear maps are equal. -/
@[ext]
theorem hom_ext {X Y : FiniteProjective.{uR, uM} R} {f g : X ⟶ Y}
    (h : f.hom.hom = g.hom.hom) : f = g :=
  ObjectProperty.hom_ext _ (ModuleCat.hom_ext h)

/-- Morphisms in `ModuleCat.FiniteProjective R` are the underlying linear maps. -/
def homLinearEquiv (X Y : FiniteProjective.{uR, uM} R) :
    (X ⟶ Y) ≃ (X →ₗ[R] Y) :=
  InducedCategory.homEquiv.trans ModuleCat.homEquiv

end FiniteProjective

/-- The product of two finite projective modules is finite projective. -/
theorem finiteProjective_prod
    {P Q : Type uM} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    (hP : Module.Finite R P ∧ Module.Projective R P)
    (hQ : Module.Finite R Q ∧ Module.Projective R Q) :
    Module.Finite R (P × Q) ∧ Module.Projective R (P × Q) := by
  let _ : Module.Finite R P := hP.1
  let _ : Module.Projective R P := hP.2
  let _ : Module.Finite R Q := hQ.1
  let _ : Module.Projective R Q := hQ.2
  exact ⟨inferInstance, inferInstance⟩

instance isFiniteProjectiveIsClosedUnderIsomorphisms :
    (isFiniteProjective.{uR, uM} R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let _ : Module.Finite R X := hX.1
    let _ : Module.Projective R X := hX.2
    exact ⟨Module.Finite.equiv e.toLinearEquiv,
      Module.Projective.of_equiv' e.toLinearEquiv⟩

instance isFiniteProjectiveContainsZero :
    (isFiniteProjective.{uR, uM} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit,
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance, by
    change Module.Finite R PUnit ∧ Module.Projective R PUnit
    exact ⟨inferInstance, inferInstance⟩⟩

instance isFiniteProjectiveIsClosedUnderBinaryProducts :
    (isFiniteProjective.{uR, uM} R).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro Z ⟨p⟩
    let X := p.diag.obj ⟨WalkingPair.left⟩
    let Y := p.diag.obj ⟨WalkingPair.right⟩
    have hX : isFiniteProjective R X := p.prop_diag_obj ⟨WalkingPair.left⟩
    have hY : isFiniteProjective R Y := p.prop_diag_obj ⟨WalkingPair.right⟩
    let _ : Module.Finite R X := hX.1
    let _ : Module.Projective R X := hX.2
    let _ : Module.Finite R Y := hY.1
    let _ : Module.Projective R Y := hY.2
    let e : ModuleCat.of R (X × Y) ≅ Z := IsLimit.conePointUniqueUpToIso
      (ModuleCat.binaryProductLimitCone X Y).isLimit
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)
    exact (isFiniteProjective R).prop_of_iso e ⟨inferInstance, inferInstance⟩

instance isFiniteProjectiveIsClosedUnderFiniteProducts :
    (isFiniteProjective.{uR, uM} R).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

noncomputable instance finiteProjectiveHasFiniteBiproducts :
    HasFiniteBiproducts (FiniteProjective.{uR, uM} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end ModuleCat
