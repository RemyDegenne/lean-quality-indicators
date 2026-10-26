/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Translations in group objects

This file supplies the characteristic composition formula for right translation
and the left-translation isomorphism complementary to `CategoryTheory.GrpObj.mulRight`.

## References

* J. S. Milne, *Algebraic Groups* (2017), items 1.7–1.8, for rational
  group points and the left-translation isomorphism of algebraic groups.
  The results here apply to points `𝟙_ C ⟶ A` of an arbitrary group object;
  no closed-point transitivity is asserted.
* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, especially
  `GrpObj.mulRight` and inversion, for the group-object translation API.
-/

public section

open CategoryTheory

noncomputable section

namespace CategoryTheory.GrpObj

open MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Right translation acts on morphisms by right multiplication by the constant point. -/
@[to_additive
  /-- Right translation acts on morphisms by addition of the constant point. -/]
lemma comp_mulRight_hom {A T : C} [GrpObj A] (f : T ⟶ A) (g : 𝟙_ C ⟶ A) :
    f ≫ (mulRight g).hom = f * (toUnit T ≫ g) := by
  change f ≫ ((𝟙 A) * (toUnit A ≫ g)) = _
  simp only [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]

/-- The left-translation isomorphism `(f * ·)` of a group object.
For algebraic groups and rational points, see Milne, *Algebraic Groups* (2017), item 1.8. -/
@[to_additive /-- The left-translation isomorphism `(f + ·)` of an additive group object. -/]
def mulLeft {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A) : A ≅ A :=
  asIso ι[A] ≪≫ mulRight (f ≫ ι[A]) ≪≫ asIso ι[A]

@[to_additive (attr := simp)]
lemma mulLeft_hom {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A) :
    (mulLeft f).hom = lift (toUnit _ ≫ f) (𝟙 _) ≫ μ := by
  let _ : BraidedCategory C := .ofCartesianMonoidalCategory
  simp only [mulLeft, Iso.trans_hom, mulRight, asIso_hom, Category.assoc]
  rw [CategoryTheory.GrpObj.mul_inv_rev]
  simp [comp_lift_assoc]

/-- Left translation acts on points by left multiplication. -/
@[to_additive (attr := simp) /-- Additive left translation acts on points by addition. -/]
lemma comp_mulLeft_hom {A : C} [GrpObj A] (a x : 𝟙_ C ⟶ A) :
    x ≫ (mulLeft a).hom = a * x := by
  rw [mulLeft_hom, ← Category.assoc]
  simp [CategoryTheory.Hom.mul_def]

/-- Left translation by `a` sends the unit point to `a`. -/
@[to_additive unit_comp_addLeft_hom
  /-- Additive left translation by `a` sends the zero point to `a`. -/]
lemma unit_comp_mulLeft_hom {A : C} [GrpObj A] (a : 𝟙_ C ⟶ A) :
    η[A] ≫ (mulLeft a).hom = a := by
  rw [mulLeft_hom, ← Category.assoc]
  simp only [comp_lift, Category.comp_id]
  simpa only [comp_toUnit_assoc, toUnit_unit, Category.id_comp,
    CategoryTheory.Hom.mul_def, CategoryTheory.Hom.one_def] using (mul_one a)

/-- Composing left translation by `b` with left translation by `a` is left
translation by `a * b`. This is the categorical composition order of the
identity `lₐ ∘ lᵦ = lₐᵦ` in Milne, *Algebraic Groups* (2017), item 1.8. -/
@[to_additive
  /-- Composing additive left translation by `b` with additive left translation
  by `a` is additive left translation by `a + b`. -/]
lemma mulLeft_trans_mulLeft {A : C} [GrpObj A] (a b : 𝟙_ C ⟶ A) :
    mulLeft b ≪≫ mulLeft a = mulLeft (a * b) := by
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [mulLeft_hom, mulLeft_hom, mulLeft_hom]
  rw [← Category.assoc, comp_lift]
  simp only [Category.comp_id, comp_toUnit_assoc]
  change (toUnit A ≫ a) * ((toUnit A ≫ b) * 𝟙 A) =
    (toUnit A ≫ (a * b)) * 𝟙 A
  rw [← _root_.mul_assoc, ← MonObj.comp_mul]

@[to_additive (attr := simp)]
lemma mulLeft_one (A : C) [GrpObj A] : mulLeft η[A] = Iso.refl A := by
  ext
  simp

end CategoryTheory.GrpObj
