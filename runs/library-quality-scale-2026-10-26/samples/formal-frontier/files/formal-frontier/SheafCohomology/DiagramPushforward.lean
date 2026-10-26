/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SheafCohomology.ConePullback
public import SheafCohomology.SquareTransition

public section

/-!
# Pushforward of diagrams and cones of sheafed spaces

A natural family of continuous maps transports a contravariant diagram of
sheafed spaces to a diagram over its target spaces. Its arrows use the forward
strict pushforward comparison associated with the actual naturality square.
Compatible cones transport without any limit or Cartesian hypothesis.
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
variable [instConcrete : ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]
variable [instPreservesLimits : PreservesLimits (CategoryTheory.forget A)]
variable [instPreservesFiltered : PreservesFilteredColimits (CategoryTheory.forget A)]
variable [instReflectsIsos : (CategoryTheory.forget A).ReflectsIsomorphisms]

/-- The native sheafed space obtained by direct image along a continuous map. -/
@[expose] def diagramPushforwardObj (X : SheafedSpace A)
    {Y : TopCat.{w}} (f : (X : TopCat) ⟶ Y) : SheafedSpace A where
  carrier := Y
  presheaf := ((TopCat.Sheaf.pushforward A f).obj X.sheaf).obj
  IsSheaf := ((TopCat.Sheaf.pushforward A f).obj X.sheaf).property

/-- The sheaf map over `q` uses the forward strict square comparison. -/
@[expose] def diagramPushforwardHom {Xj Xi : SheafedSpace A}
    {Yj Yi : TopCat.{w}} (r : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : (Xi : TopCat) ⟶ Yi) (fj : (Xj : TopCat) ⟶ Yj)
    (h : r.hom.base ≫ fi = fj ≫ q) :
    diagramPushforwardObj A Xj fj ⟶ diagramPushforwardObj A Xi fi :=
  InducedCategory.homMk {
    base := q
    c := ((TopCat.Sheaf.pushforward A fi).map (⟨r.hom.c⟩ :
      Xi.sheaf ⟶ (TopCat.Sheaf.pushforward A r.hom.base).obj Xj.sheaf) ≫
      (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
        r.hom.base q fi fj h).hom.app Xj.sheaf).hom }

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforwardObj_carrier (X : SheafedSpace A)
    {Y : TopCat.{w}} (f : (X : TopCat) ⟶ Y) :
    (diagramPushforwardObj A X f : TopCat) = Y := rfl

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforwardObj_sheaf (X : SheafedSpace A)
    {Y : TopCat.{w}} (f : (X : TopCat) ⟶ Y) :
    (diagramPushforwardObj A X f).sheaf =
      (TopCat.Sheaf.pushforward A f).obj X.sheaf := rfl

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforwardHom_base {Xj Xi : SheafedSpace A}
    {Yj Yi : TopCat.{w}} (r : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : (Xi : TopCat) ⟶ Yi) (fj : (Xj : TopCat) ⟶ Yj)
    (h : r.hom.base ≫ fi = fj ≫ q) :
    (diagramPushforwardHom A r q fi fj h).hom.base = q := rfl

omit [HasColimits A] [HasLimits A] in
theorem diagramPushforwardHom_sheafMap {Xj Xi : SheafedSpace A}
    {Yj Yi : TopCat.{w}} (r : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : (Xi : TopCat) ⟶ Yi) (fj : (Xj : TopCat) ⟶ Yj)
    (h : r.hom.base ≫ fi = fj ≫ q) :
    (⟨(diagramPushforwardHom A r q fi fj h).hom.c⟩ :
      (TopCat.Sheaf.pushforward A fi).obj Xi.sheaf ⟶
        (TopCat.Sheaf.pushforward A q).obj
          ((TopCat.Sheaf.pushforward A fj).obj Xj.sheaf)) =
      (TopCat.Sheaf.pushforward A fi).map (⟨r.hom.c⟩ :
        Xi.sheaf ⟶ (TopCat.Sheaf.pushforward A r.hom.base).obj Xj.sheaf) ≫
        (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
          r.hom.base q fi fj h).hom.app Xj.sheaf := rfl

/-- The mate of the actual native arrow agrees with the transported square transition. -/
theorem diagramPushforwardHom_mate {Xj Xi : SheafedSpace A}
    {Yj Yi : TopCat.{w}} (r : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : (Xi : TopCat) ⟶ Yi) (fj : (Xj : TopCat) ⟶ Yj)
    (h : r.hom.base ≫ fi = fj ≫ q) :
    sheafMate A (diagramPushforwardHom A r q fi fj h) =
      TopCat.Sheaf.SquareTransition.transition A r.hom.base q fi fj h
        (sheafMate A r) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv _ _).injective
  have hAdj := TopCat.Sheaf.SquareTransition.adjoint_transition A
    r.hom.base q fi fj h (sheafMate A r)
  simp only [TopCat.Sheaf.SquareTransition.adjoint_eq_homEquiv,
    sheafMate_adjoint] at hAdj
  exact (sheafMate_adjoint A (diagramPushforwardHom A r q fi fj h)).trans
    ((diagramPushforwardHom_sheafMap A r q fi fj h).trans hAdj.symm)

omit [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] instConcrete
  [HasColimits A] [HasLimits A] instPreservesLimits instPreservesFiltered instReflectsIsos in
theorem diagramPushforwardHom_id (X : SheafedSpace A)
    {Y : TopCat.{w}} (f : (X : TopCat) ⟶ Y) :
    diagramPushforwardHom A (𝟙 X) (𝟙 Y) f f (by simp) =
      𝟙 (diagramPushforwardObj A X f) := by
  apply InducedCategory.hom_ext
  apply PresheafedSpace.hext _ _ (by rfl)
  apply heq_of_eq
  change ((TopCat.Sheaf.pushforward A f).map (⟨(𝟙 X : X ⟶ X).hom.c⟩ :
      X.sheaf ⟶ (TopCat.Sheaf.pushforward A (𝟙 (X : TopCat))).obj X.sheaf) ≫
      (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
        (𝟙 (X : TopCat)) (𝟙 Y) f f (by simp)).hom.app X.sheaf).hom =
      (𝟙 ((TopCat.Sheaf.pushforward A f).obj X.sheaf) :
        (TopCat.Sheaf.pushforward A f).obj X.sheaf ⟶ _).hom
  have hid : (⟨(𝟙 X : X ⟶ X).hom.c⟩ :
      X.sheaf ⟶ (TopCat.Sheaf.pushforward A (𝟙 (X : TopCat))).obj X.sheaf) =
        𝟙 X.sheaf := by
    apply CategoryTheory.Sheaf.hom_ext
    rfl
  have hsq : (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
      (𝟙 (X : TopCat)) (𝟙 Y) f f (by simp)).hom.app X.sheaf =
        𝟙 ((TopCat.Sheaf.pushforward A f).obj X.sheaf) := by
    rw [TopCat.Sheaf.SquareTransition.pushforwardSquareIso_hom_eq, eqToHom_app]
    apply eqToHom_refl
  have hmap : (TopCat.Sheaf.pushforward A f).map (⟨(𝟙 X : X ⟶ X).hom.c⟩ :
      X.sheaf ⟶ (TopCat.Sheaf.pushforward A (𝟙 (X : TopCat))).obj X.sheaf) =
        𝟙 ((TopCat.Sheaf.pushforward A f).obj X.sheaf) :=
    (congrArg (TopCat.Sheaf.pushforward A f).map hid).trans
      ((TopCat.Sheaf.pushforward A f).map_id X.sheaf)
  have hsheaf :
      (TopCat.Sheaf.pushforward A f).map (⟨(𝟙 X : X ⟶ X).hom.c⟩ :
        X.sheaf ⟶ (TopCat.Sheaf.pushforward A (𝟙 (X : TopCat))).obj X.sheaf) ≫
        (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
          (𝟙 (X : TopCat)) (𝟙 Y) f f (by simp)).hom.app X.sheaf =
      𝟙 ((TopCat.Sheaf.pushforward A f).obj X.sheaf) := by
    calc
      _ = (𝟙 ((TopCat.Sheaf.pushforward A f).obj X.sheaf)) ≫
          (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
            (𝟙 (X : TopCat)) (𝟙 Y) f f (by simp)).hom.app X.sheaf :=
          congrArg (· ≫ _) hmap
      _ = 𝟙 _ ≫ 𝟙 _ := congrArg (𝟙 _ ≫ ·) hsq
      _ = _ := Category.id_comp _
  exact congrArg (fun m => m.hom) hsheaf

omit [HasColimits A] [HasLimits A] in
/-- Native composition uses the pasted square, rather than an assumed coherence axiom. -/
theorem diagramPushforwardHom_comp {Xk Xj Xi : SheafedSpace A}
    {Yk Yj Yi : TopCat.{w}} (rjk : Xk ⟶ Xj) (rij : Xj ⟶ Xi)
    (qjk : Yk ⟶ Yj) (qij : Yj ⟶ Yi)
    (fi : (Xi : TopCat) ⟶ Yi) (fj : (Xj : TopCat) ⟶ Yj)
    (fk : (Xk : TopCat) ⟶ Yk)
    (hij : rij.hom.base ≫ fi = fj ≫ qij)
    (hjk : rjk.hom.base ≫ fj = fk ≫ qjk) :
    diagramPushforwardHom A rjk qjk fj fk hjk ≫
        diagramPushforwardHom A rij qij fi fj hij =
      diagramPushforwardHom A (rjk ≫ rij) (qjk ≫ qij) fi fk
        (by
          change (rjk.hom.base ≫ rij.hom.base) ≫ fi = fk ≫ (qjk ≫ qij)
          rw [Category.assoc, hij, ← Category.assoc, hjk, Category.assoc]) := by
  have hnative : (⟨(rjk ≫ rij).hom.c⟩ : Xi.sheaf ⟶
      (TopCat.Sheaf.pushforward A (rjk.hom.base ≫ rij.hom.base)).obj Xk.sheaf) =
        (⟨rij.hom.c⟩ : Xi.sheaf ⟶
          (TopCat.Sheaf.pushforward A rij.hom.base).obj Xj.sheaf) ≫
          (TopCat.Sheaf.pushforward A rij.hom.base).map
            (⟨rjk.hom.c⟩ : Xj.sheaf ⟶
              (TopCat.Sheaf.pushforward A rjk.hom.base).obj Xk.sheaf) := by
    apply CategoryTheory.Sheaf.hom_ext
    rfl
  have hsq :
      (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
        rij.hom.base qij fi fj hij).hom.app
          ((TopCat.Sheaf.pushforward A rjk.hom.base).obj Xk.sheaf) ≫
        (TopCat.Sheaf.pushforward A qij).map
          ((TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
            rjk.hom.base qjk fj fk hjk).hom.app Xk.sheaf) =
      (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
        (rjk.hom.base ≫ rij.hom.base) (qjk ≫ qij) fi fk
        (by rw [Category.assoc, hij, ← Category.assoc, hjk, Category.assoc])).hom.app
          Xk.sheaf := by
    simp only [TopCat.Sheaf.SquareTransition.pushforwardSquareIso_hom_eq, eqToHom_app]
    erw [eqToHom_map]
    erw [eqToHom_trans]
    rfl
  have hmaps :
      (TopCat.Sheaf.pushforward A fi).map (⟨(rjk ≫ rij).hom.c⟩ : Xi.sheaf ⟶
        (TopCat.Sheaf.pushforward A (rjk.hom.base ≫ rij.hom.base)).obj Xk.sheaf) ≫
          (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
            (rjk.hom.base ≫ rij.hom.base) (qjk ≫ qij) fi fk
            (by rw [Category.assoc, hij, ← Category.assoc, hjk, Category.assoc])).hom.app
              Xk.sheaf =
        ((TopCat.Sheaf.pushforward A fi).map (⟨rij.hom.c⟩ : Xi.sheaf ⟶
          (TopCat.Sheaf.pushforward A rij.hom.base).obj Xj.sheaf) ≫
            (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
              rij.hom.base qij fi fj hij).hom.app Xj.sheaf) ≫
          (TopCat.Sheaf.pushforward A qij).map
            ((TopCat.Sheaf.pushforward A fj).map (⟨rjk.hom.c⟩ : Xj.sheaf ⟶
              (TopCat.Sheaf.pushforward A rjk.hom.base).obj Xk.sheaf) ≫
                (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
                  rjk.hom.base qjk fj fk hjk).hom.app Xk.sheaf) := by
    rw [hnative]
    erw [Functor.map_comp]
    erw [Functor.map_comp]
    simp only [Category.assoc]
    rw [← hsq]
    have hnat := (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
      rij.hom.base qij fi fj hij).hom.naturality
        (⟨rjk.hom.c⟩ : Xj.sheaf ⟶
          (TopCat.Sheaf.pushforward A rjk.hom.base).obj Xk.sheaf)
    simp only [Functor.comp_map] at hnat
    conv_lhs =>
      arg 2
      erw [← Category.assoc]
    erw [hnat]
    simp only [Category.assoc]
    rfl
  apply InducedCategory.hom_ext
  apply PresheafedSpace.hext _ _ (by rfl)
  apply heq_of_eq
  exact congrArg (fun m => m.hom) hmaps.symm

variable {J : Type wj} [Category.{vj} J]

omit [HasColimits A] [HasLimits A] in
/-- The naturality square in the variance of a contravariant diagram. -/
theorem diagramPushforward_square (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    {i j : Jᵒᵖ} (a : i ⟶ j) :
    (N.map a).hom.base ≫ f.app j = f.app i ≫ Y.map a :=
  f.naturality a

/-- The actual stage arrow and its naturality square determine the target arrow. -/
@[expose] def diagramPushforwardMap (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    {i j : Jᵒᵖ} (a : i ⟶ j) :
    diagramPushforwardObj A (N.obj i) (f.app i) ⟶
      diagramPushforwardObj A (N.obj j) (f.app j) :=
  diagramPushforwardHom A (N.map a) (Y.map a) (f.app j) (f.app i)
    (diagramPushforward_square A N Y f a)

omit [HasColimits A] [HasLimits A] in
theorem diagramPushforwardMap_id (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y) (i : Jᵒᵖ) :
    diagramPushforwardMap A N Y f (𝟙 i) =
      𝟙 (diagramPushforwardObj A (N.obj i) (f.app i)) := by
  simpa only [diagramPushforwardMap, N.map_id, Y.map_id] using
    (diagramPushforwardHom_id A (N.obj i) (f.app i))

omit [HasColimits A] [HasLimits A] in
theorem diagramPushforwardMap_comp (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    {i j k : Jᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    diagramPushforwardMap A N Y f (a ≫ b) =
      diagramPushforwardMap A N Y f a ≫ diagramPushforwardMap A N Y f b := by
  have hcomp : (N.map a ≫ N.map b).hom.base ≫ f.app k =
      f.app i ≫ (Y.map a ≫ Y.map b) := by
    rw [← N.map_comp, ← Y.map_comp]
    exact diagramPushforward_square A N Y f (a ≫ b)
  calc
    diagramPushforwardMap A N Y f (a ≫ b) =
        diagramPushforwardHom A (N.map a ≫ N.map b)
          (Y.map a ≫ Y.map b) (f.app k) (f.app i) hcomp := by
            simp only [diagramPushforwardMap, N.map_comp, Y.map_comp]
    _ = diagramPushforwardMap A N Y f a ≫
        diagramPushforwardMap A N Y f b := by
          exact (diagramPushforwardHom_comp A (N.map a) (N.map b)
            (Y.map a) (Y.map b) (f.app k) (f.app j) (f.app i)
            (diagramPushforward_square A N Y f b)
            (diagramPushforward_square A N Y f a)).symm

/-- The native diagram of sheafed spaces over the target topological diagram. -/
@[expose] def diagramPushforward (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y) :
    Jᵒᵖ ⥤ SheafedSpace A where
  obj i := diagramPushforwardObj A (N.obj i) (f.app i)
  map a := diagramPushforwardMap A N Y f a
  map_id := diagramPushforwardMap_id A N Y f
  map_comp := diagramPushforwardMap_comp A N Y f

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforward_obj (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y) (i : Jᵒᵖ) :
    (diagramPushforward A N Y f).obj i = diagramPushforwardObj A (N.obj i) (f.app i) := rfl

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforward_map (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    {i j : Jᵒᵖ} (a : i ⟶ j) :
    (diagramPushforward A N Y f).map a =
      diagramPushforwardHom A (N.map a) (Y.map a) (f.app j) (f.app i)
        (diagramPushforward_square A N Y f a) := rfl

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforward_obj_carrier (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y) (i : Jᵒᵖ) :
    ((diagramPushforward A N Y f).obj i : TopCat) = Y.obj i := rfl

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforward_obj_sheaf (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y) (i : Jᵒᵖ) :
    ((diagramPushforward A N Y f).obj i).sheaf =
      (TopCat.Sheaf.pushforward A (f.app i)).obj (N.obj i).sheaf := rfl

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforward_map_base (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    {i j : Jᵒᵖ} (a : i ⟶ j) :
    ((diagramPushforward A N Y f).map a).hom.base = Y.map a := rfl

omit [HasColimits A] [HasLimits A] in
/-- The diagram arrow is the actual sheaf map followed by the forward strict square map. -/
theorem diagramPushforward_map_sheafMap (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    {i j : Jᵒᵖ} (a : i ⟶ j) :
    (⟨((diagramPushforward A N Y f).map a).hom.c⟩ :
      (TopCat.Sheaf.pushforward A (f.app j)).obj (N.obj j).sheaf ⟶
        (TopCat.Sheaf.pushforward A (Y.map a)).obj
          ((TopCat.Sheaf.pushforward A (f.app i)).obj (N.obj i).sheaf)) =
      (TopCat.Sheaf.pushforward A (f.app j)).map (⟨(N.map a).hom.c⟩ :
        (N.obj j).sheaf ⟶ (TopCat.Sheaf.pushforward A
          (N.map a).hom.base).obj (N.obj i).sheaf) ≫
        (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
          (N.map a).hom.base (Y.map a) (f.app j) (f.app i)
          (diagramPushforward_square A N Y f a)).hom.app (N.obj i).sheaf :=
  diagramPushforwardHom_sheafMap A (N.map a) (Y.map a)
    (f.app j) (f.app i) (diagramPushforward_square A N Y f a)

/-- The actual diagram arrow mate is the canonical square transition of the source mate. -/
theorem diagramPushforward_map_mate (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    {i j : Jᵒᵖ} (a : i ⟶ j) :
    sheafMate A ((diagramPushforward A N Y f).map a) =
      TopCat.Sheaf.SquareTransition.transition A (N.map a).hom.base
        (Y.map a) (f.app j) (f.app i)
        (diagramPushforward_square A N Y f a) (sheafMate A (N.map a)) :=
  diagramPushforwardHom_mate A (N.map a) (Y.map a)
    (f.app j) (f.app i) (diagramPushforward_square A N Y f a)

/-- A compatible cone of spaces receives the pushforward of a native cone. -/
@[expose] def diagramPushforwardCone (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) :
    Cone (diagramPushforward A N Y f) where
  pt := diagramPushforwardObj A c.pt g
  π := {
    app := fun i ↦ diagramPushforwardHom A (c.π.app i) (d.π.app i)
      (f.app i) g (h i)
    naturality := by
      intro i j a
      have hcomp := diagramPushforwardHom_comp A (c.π.app i) (N.map a)
        (d.π.app i) (Y.map a) (f.app j) (f.app i) g
        (diagramPushforward_square A N Y f a) (h i)
      simp only [c.w a, d.w a] at hcomp
      change 𝟙 _ ≫ diagramPushforwardHom A (c.π.app j) (d.π.app j) (f.app j) g
          (h j) = diagramPushforwardHom A (c.π.app i) (d.π.app i)
            (f.app i) g (h i) ≫ diagramPushforwardHom A (N.map a) (Y.map a)
              (f.app j) (f.app i) (diagramPushforward_square A N Y f a)
      simpa only [Category.id_comp] using hcomp.symm }

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforwardCone_pt (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) :
    (diagramPushforwardCone A N Y f c d g h).pt = diagramPushforwardObj A c.pt g := rfl

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforwardCone_projection (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) (i : Jᵒᵖ) :
    (diagramPushforwardCone A N Y f c d g h).π.app i =
      diagramPushforwardHom A (c.π.app i) (d.π.app i) (f.app i) g (h i) := rfl

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforwardCone_carrier (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) :
    ((diagramPushforwardCone A N Y f c d g h).pt : TopCat) = d.pt := rfl

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforwardCone_sheaf (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) :
    (diagramPushforwardCone A N Y f c d g h).pt.sheaf =
      (TopCat.Sheaf.pushforward A g).obj c.pt.sheaf := rfl

omit [HasColimits A] [HasLimits A] in
@[simp] theorem diagramPushforwardCone_projection_base (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i)
    (i : Jᵒᵖ) :
    ((diagramPushforwardCone A N Y f c d g h).π.app i).hom.base =
      d.π.app i := rfl

omit [HasColimits A] [HasLimits A] in
/-- Native projection sheaf map: direct image of the source projection, then the strict square. -/
theorem diagramPushforwardCone_projection_sheafMap (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i)
    (i : Jᵒᵖ) :
    (⟨((diagramPushforwardCone A N Y f c d g h).π.app i).hom.c⟩ :
      (TopCat.Sheaf.pushforward A (f.app i)).obj (N.obj i).sheaf ⟶
        (TopCat.Sheaf.pushforward A (d.π.app i)).obj
          ((TopCat.Sheaf.pushforward A g).obj c.pt.sheaf)) =
      (TopCat.Sheaf.pushforward A (f.app i)).map (⟨(c.π.app i).hom.c⟩ :
        (N.obj i).sheaf ⟶
          (TopCat.Sheaf.pushforward A (c.π.app i).hom.base).obj c.pt.sheaf) ≫
        (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
          (c.π.app i).hom.base (d.π.app i) (f.app i) g (h i)).hom.app c.pt.sheaf :=
  diagramPushforwardHom_sheafMap A (c.π.app i) (d.π.app i)
    (f.app i) g (h i)

/-- The mate of the actual native projection is the transition of the source projection mate. -/
theorem diagramPushforwardCone_projection_mate (N : Jᵒᵖ ⥤ SheafedSpace A)
    (Y : Jᵒᵖ ⥤ TopCat.{w}) (f : N ⋙ forget A ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i)
    (i : Jᵒᵖ) :
    sheafMate A ((diagramPushforwardCone A N Y f c d g h).π.app i) =
      TopCat.Sheaf.SquareTransition.transition A (c.π.app i).hom.base
        (d.π.app i) (f.app i) g (h i) (sheafMate A (c.π.app i)) :=
  diagramPushforwardHom_mate A (c.π.app i) (d.π.app i) (f.app i) g (h i)

end AlgebraicGeometry.SheafedSpace
