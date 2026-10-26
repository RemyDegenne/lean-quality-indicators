/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
import Mathlib.CategoryTheory.Limits.Over

/-!
# Density in over-categories

The functor `CostructuredArrow.toOver F X` sends a probe `F.obj a ⟶ X` to
that same arrow as an object of `Over X`. If `F` is dense at the underlying
object, then this functor is dense at the object over `X`. In particular,
slicing a dense functor gives a dense functor.

The canonical probe categories are compared by
`CostructuredArrow.costructuredArrowToOverEquivalence`. No fullness or
faithfulness assumption on `F` is needed.

## References

* Mathlib, `CategoryTheory.Comma.Over.Basic`, for the slice functor and the
  comparison of its costructured-arrow categories.
* Joël Riou's Mathlib `CategoryTheory.Functor.KanExtension.DenseAt` and
  `Dense`, for density as the canonical-colimit universal property.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe vA vC uA uC

namespace CategoryTheory.CostructuredArrow

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Density of a functor at an underlying object implies density of the sliced
functor at the corresponding object of the over-category. -/
theorem isDenseAt_toOver
    {A : Type uA} {C : Type uC} [Category.{vA} A] [Category.{vC} C]
    (F : A ⥤ C) (X : C) (Y : Over X) :
    F.isDenseAt Y.left → (toOver F X).isDenseAt Y := by
  intro h
  rw [Functor.isDenseAt_iff] at h ⊢
  obtain ⟨h⟩ := h
  refine ⟨Limits.isColimitOfReflects (Over.forget X) ?_⟩
  let e := costructuredArrowToOverEquivalence F Y
  let i : e.functor ⋙ (CostructuredArrow.proj F Y.left ⋙ F) ≅
      (CostructuredArrow.proj (toOver F X) Y ⋙ toOver F X) ⋙ Over.forget X :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro Z Z' f
      change F.map f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ F.map f.left.left
      simp only [Category.comp_id, Category.id_comp])
  -- The comparison identifies the underlying canonical cocones, not just their points.
  refine (Limits.IsColimit.equivOfNatIsoOfIso i _ _ ?_) (h.whiskerEquivalence e)
  exact Limits.Cocone.ext (Iso.refl _) (by
    intro j
    change (𝟙 _ ≫ (𝟙 _ ≫ j.hom.left)) ≫ 𝟙 _ = 𝟙 _ ≫ j.hom.left
    simp only [Category.id_comp, Category.comp_id])

/-- Slicing a dense functor over any object gives a dense functor. -/
instance isDense_toOver
    {A : Type uA} {C : Type uC} [Category.{vA} A] [Category.{vC} C]
    (F : A ⥤ C) [F.IsDense] (X : C) :
    (toOver F X).IsDense := by
  constructor
  intro Y
  exact isDenseAt_toOver F X Y (Functor.IsDense.isDenseAt F Y.left)

end CategoryTheory.CostructuredArrow
