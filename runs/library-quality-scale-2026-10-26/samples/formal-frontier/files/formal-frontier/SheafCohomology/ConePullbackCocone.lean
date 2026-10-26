/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.ConePullback

public section

/-!
# The cocone induced by a native cone of sheafed spaces

Pulling the stages of a native cone back to its vertex gives a cocone of sheaves.
Its legs are the inverse-image mates of the actual cone projections.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u vj wj

namespace AlgebraicGeometry.SheafedSpace

variable (A : Type u) [Category.{w} A]
variable {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- Mates of native arrows respect any commuting triangle of sheafed spaces. -/
theorem sheafMate_triangle {W X Y : SheafedSpace A}
    (p : W ⟶ X) (q : W ⟶ Y) (f : Y ⟶ X) (h : q ≫ f = p) :
    triangleMap A (congrArg (fun g : W ⟶ X ↦ g.hom.base) h) (sheafMate A f) ≫
      sheafMate A q = sheafMate A p := by
  cases h
  simp [triangleMap, sheafMate_comp, Category.assoc]

variable {J : Type wj} [Category.{vj} J]

/-- The canonical sheaf cocone of a native cone, with no limiting assumption. -/
@[expose] def conePullbackCocone (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone S) : Cocone (conePullback A S ((forget A).mapCone c)) where
  pt := c.pt.sheaf
  ι := {
    app := fun i ↦ sheafMate A (c.π.app (op i))
    naturality := by
      intro i j a
      change (conePullback A S ((forget A).mapCone c)).map a ≫
        sheafMate A (c.π.app (op j)) =
          sheafMate A (c.π.app (op i)) ≫ 𝟙 _
      rw [Category.comp_id]
      rw [conePullback_map]
      exact sheafMate_triangle A (c.π.app (op i))
        (c.π.app (op j)) (S.map a.op) (c.w a.op) }

@[simp] theorem conePullbackCocone_pt (S : Jᵒᵖ ⥤ SheafedSpace A) (c : Cone S) :
    (conePullbackCocone A S c).pt = c.pt.sheaf := rfl

@[simp] theorem conePullbackCocone_ι_app (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone S) (i : J) :
    (conePullbackCocone A S c).ι.app i = sheafMate A (c.π.app (op i)) := rfl

/-- Naturality is the literal native triangle law for the mates of the projections. -/
theorem conePullbackCocone_triangle (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone S) {i j : J} (a : i ⟶ j) :
    (conePullback A S ((forget A).mapCone c)).map a ≫
      sheafMate A (c.π.app (op j)) = sheafMate A (c.π.app (op i)) := by
  rw [conePullback_map]
  exact sheafMate_triangle A (c.π.app (op i))
    (c.π.app (op j)) (S.map a.op) (c.w a.op)

end AlgebraicGeometry.SheafedSpace
