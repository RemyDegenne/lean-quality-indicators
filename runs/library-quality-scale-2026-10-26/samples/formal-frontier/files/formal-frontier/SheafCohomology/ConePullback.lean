/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import SheafCohomology.PullbackCoherence

public section

/-!
# Pulling a sheafed-space diagram to a cone

A cone over the underlying spaces of a contravariant diagram of sheafed spaces
pulls its stage sheaves back to one space. The transition maps are mates of the
actual sheafed-space morphisms, transported across the cone triangles.
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

/-- The native inverse-image mate of a sheafed-space arrow. -/
@[expose] def sheafMate {X Y : SheafedSpace A} (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback A f.hom.base).obj Y.sheaf ⟶ X.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction A f.hom.base).homEquiv _ _).symm
    ⟨f.hom.c⟩

/-- The mate recovers the actual sheaf map of a sheafed-space arrow. -/
theorem sheafMate_adjoint {X Y : SheafedSpace A} (f : X ⟶ Y) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction A f.hom.base).homEquiv _ _
      (sheafMate A f) = (⟨f.hom.c⟩ : Y.sheaf ⟶
        (TopCat.Sheaf.pushforward A f.hom.base).obj X.sheaf) :=
  Equiv.apply_symm_apply _ _

theorem sheafMate_id (X : SheafedSpace A) :
    sheafMate A (𝟙 X) = TopCat.Sheaf.pullbackIdHom A (X : TopCat) X.sheaf := by
  let adjDirect : TopCat.Sheaf.pullback A (𝟙 (X : TopCat)) ⊣
      𝟭 ((X : TopCat).Sheaf A) :=
    TopCat.Sheaf.pullbackPushforwardAdjunction A (𝟙 (X : TopCat))
  have hId : (⟨(𝟙 X : X ⟶ X).hom.c⟩ : X.sheaf ⟶ X.sheaf) = 𝟙 X.sheaf := by
    apply CategoryTheory.Sheaf.hom_ext
    rfl
  have hcanon : adjDirect.homEquiv X.sheaf X.sheaf
      ((Adjunction.leftAdjointUniq Adjunction.id adjDirect).inv.app X.sheaf) =
        𝟙 X.sheaf := by
    rw [Adjunction.leftAdjointUniq_inv_app]
    simpa using
      (Adjunction.homEquiv_leftAdjointUniq_hom_app adjDirect Adjunction.id X.sheaf)
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction A (𝟙 X : X ⟶ X).hom.base).homEquiv _ _).injective
  rw [sheafMate_adjoint]
  calc
    (⟨(𝟙 X : X ⟶ X).hom.c⟩ : X.sheaf ⟶ X.sheaf) = 𝟙 X.sheaf := hId
    _ = _ := by
      change 𝟙 X.sheaf = adjDirect.homEquiv X.sheaf X.sheaf
        ((Adjunction.leftAdjointUniq Adjunction.id adjDirect).inv.app X.sheaf)
      exact hcanon.symm

private theorem mateComp {W X Y : TopCat.{w}} (f : W ⟶ X) (g : X ⟶ Y)
    {F : Y.Sheaf A} {G : X.Sheaf A} {H : W.Sheaf A}
    (b : (TopCat.Sheaf.pullback A g).obj F ⟶ G)
    (a : (TopCat.Sheaf.pullback A f).obj G ⟶ H) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction A (f ≫ g)).homEquiv F H
      (TopCat.Sheaf.pullbackCompInv A f g F ≫
        (TopCat.Sheaf.pullback A f).map b ≫ a) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction A g).homEquiv F G b ≫
        (TopCat.Sheaf.pushforward A g).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).homEquiv G H a) := by
  let adjComp := (TopCat.Sheaf.pullbackPushforwardAdjunction A g).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction A f)
  let adjDirect : TopCat.Sheaf.pullback A (f ≫ g) ⊣
      (TopCat.Sheaf.pushforward A f ⋙ TopCat.Sheaf.pushforward A g) :=
    TopCat.Sheaf.pullbackPushforwardAdjunction A (f ≫ g)
  change adjDirect.homEquiv F H
      ((Adjunction.leftAdjointUniq adjComp adjDirect).inv.app F ≫
        ((TopCat.Sheaf.pullback A f).map b ≫ a)) = _
  rw [adjDirect.homEquiv_naturality_right]
  rw [Adjunction.leftAdjointUniq_inv_app]
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [← adjComp.homEquiv_unit]
  rw [Adjunction.comp_homEquiv]
  change
    ((TopCat.Sheaf.pullbackPushforwardAdjunction A g).homEquiv F
      ((TopCat.Sheaf.pushforward A f).obj H))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction A f).homEquiv
        ((TopCat.Sheaf.pullback A g).obj F) H)
        ((TopCat.Sheaf.pullback A f).map b ≫ a)) =
    ((TopCat.Sheaf.pullbackPushforwardAdjunction A g).homEquiv F G) b ≫
      (TopCat.Sheaf.pushforward A g).map
        (((TopCat.Sheaf.pullbackPushforwardAdjunction A f).homEquiv G H) a)
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction A f).homEquiv_naturality_left]
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction A g).homEquiv_naturality_right]

theorem sheafMate_comp {X Y Z : SheafedSpace A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sheafMate A (f ≫ g) =
      TopCat.Sheaf.pullbackCompInv A f.hom.base g.hom.base Z.sheaf ≫
        (TopCat.Sheaf.pullback A f.hom.base).map (sheafMate A g) ≫
        sheafMate A f := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction A
    (f ≫ g).hom.base).homEquiv _ _).injective
  rw [sheafMate_adjoint]
  have hmate := mateComp A f.hom.base g.hom.base (sheafMate A g) (sheafMate A f)
  rw [sheafMate_adjoint, sheafMate_adjoint] at hmate
  convert hmate.symm using 1; rfl

/-- Transport a stage transition across a commuting triangle of spaces. -/
@[expose] def triangleMap {W X Y : TopCat.{w}} {p : W ⟶ X} {q : W ⟶ Y} {f : Y ⟶ X}
    {F : X.Sheaf A} {G : Y.Sheaf A} (triangle : q ≫ f = p)
    (a : (TopCat.Sheaf.pullback A f).obj F ⟶ G) :
    (TopCat.Sheaf.pullback A p).obj F ⟶
      (TopCat.Sheaf.pullback A q).obj G := by
  rw [← triangle]
  exact TopCat.Sheaf.pullbackCompInv A q f F ≫
    (TopCat.Sheaf.pullback A q).map a

theorem triangleMap_id {W X : TopCat.{w}} (p : W ⟶ X) (F : X.Sheaf A) :
    triangleMap A (Category.comp_id p) (TopCat.Sheaf.pullbackIdHom A X F) =
      𝟙 ((TopCat.Sheaf.pullback A p).obj F) := by
  change triangleMap A (rfl : p ≫ 𝟙 X = p) (TopCat.Sheaf.pullbackIdHom A X F) = _
  simp [triangleMap, TopCat.Sheaf.pullbackCompInv,
    TopCat.Sheaf.pullbackCompIso_id_comp, TopCat.Sheaf.pullbackIdHom]
  refine ((TopCat.Sheaf.pullback A p).map_comp _ _).symm.trans ?_
  rw [Iso.inv_hom_id_app]
  exact (TopCat.Sheaf.pullback A p).map_id F

set_option backward.isDefEq.respectTransparency.types false in
private theorem compInv_assoc {W X Y Z : TopCat.{w}}
    (r : W ⟶ Z) (g : Z ⟶ Y) (f : Y ⟶ X) (F : X.Sheaf A) :
    TopCat.Sheaf.pullbackCompInv A r (g ≫ f) F ≫
      (TopCat.Sheaf.pullback A r).map (TopCat.Sheaf.pullbackCompInv A g f F) =
    TopCat.Sheaf.pullbackCompInv A (r ≫ g) f F ≫
      TopCat.Sheaf.pullbackCompInv A r g ((TopCat.Sheaf.pullback A f).obj F) := by
  have hc := congrArg (fun e ↦ e.inv.app F)
    (TopCat.Sheaf.pullbackCompIso_assoc A r g f)
  have hRight :
      (Functor.isoWhiskerRight (TopCat.Sheaf.pullbackCompIso A g f)
          (TopCat.Sheaf.pullback A r)).inv.app F =
        (TopCat.Sheaf.pullback A r).map
          ((TopCat.Sheaf.pullbackCompIso A g f).inv.app F) := rfl
  have hLeft :
      ((TopCat.Sheaf.pullback A f).isoWhiskerLeft
          (TopCat.Sheaf.pullbackCompIso A r g)).inv.app F =
        (TopCat.Sheaf.pullbackCompIso A r g).inv.app
          ((TopCat.Sheaf.pullback A f).obj F) := rfl
  have hAssociator :
      ((TopCat.Sheaf.pullback A f).associator (TopCat.Sheaf.pullback A g)
        (TopCat.Sheaf.pullback A r)).symm.inv.app F = 𝟙 _ := rfl
  simpa only [TopCat.Sheaf.pullbackCompInv, Iso.trans_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app,
    hRight, hLeft, hAssociator, Category.id_comp, Category.comp_id]
    using hc.symm

/-- Component associativity of the inverse comparison between direct and iterated
inverse-image functors. -/
theorem pullbackCompInv_assoc {W X Y Z : TopCat.{w}}
    (r : W ⟶ X) (q : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Sheaf A) :
    TopCat.Sheaf.pullbackCompInv A r (q ≫ g) F ≫
        (TopCat.Sheaf.pullback A r).map (TopCat.Sheaf.pullbackCompInv A q g F) =
      TopCat.Sheaf.pullbackCompInv A (r ≫ q) g F ≫
        TopCat.Sheaf.pullbackCompInv A r q ((TopCat.Sheaf.pullback A g).obj F) :=
  compInv_assoc A r q g F

set_option backward.isDefEq.respectTransparency.types false in
private theorem triangleMap_comp_aux {W X Y Z : TopCat.{w}}
    (r : W ⟶ Z) (g : Z ⟶ Y) (f : Y ⟶ X)
    {F : X.Sheaf A} {G : Y.Sheaf A} {H : Z.Sheaf A}
    (a : (TopCat.Sheaf.pullback A f).obj F ⟶ G)
    (b : (TopCat.Sheaf.pullback A g).obj G ⟶ H) :
    TopCat.Sheaf.pullbackCompInv A (r ≫ g) f F ≫
        (TopCat.Sheaf.pullback A (r ≫ g)).map a ≫
        TopCat.Sheaf.pullbackCompInv A r g G ≫
        (TopCat.Sheaf.pullback A r).map b =
      TopCat.Sheaf.pullbackCompInv A r (g ≫ f) F ≫
        (TopCat.Sheaf.pullback A r).map
        (TopCat.Sheaf.pullbackCompInv A g f F ≫
          (TopCat.Sheaf.pullback A g).map a ≫ b) := by
  simp only [Functor.map_comp]
  rw [← Category.assoc ((TopCat.Sheaf.pullback A (r ≫ g)).map a)
    (TopCat.Sheaf.pullbackCompInv A r g G) ((TopCat.Sheaf.pullback A r).map b)]
  rw [TopCat.Sheaf.pullbackCompInv_naturality A r g a]
  simp only [Category.assoc]
  rw [← Category.assoc (TopCat.Sheaf.pullbackCompInv A (r ≫ g) f F)
    (TopCat.Sheaf.pullbackCompInv A r g ((TopCat.Sheaf.pullback A f).obj F))]
  rw [← compInv_assoc A r g f F]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- Pulling successive triangle transitions to the common vertex respects composition. -/
theorem triangleMap_comp {W X Y Z : TopCat.{w}}
    {p : W ⟶ X} {q : W ⟶ Y} {r : W ⟶ Z}
    {f : Y ⟶ X} {g : Z ⟶ Y}
    {F : X.Sheaf A} {G : Y.Sheaf A} {H : Z.Sheaf A}
    (hp : q ≫ f = p) (hq : r ≫ g = q)
    (a : (TopCat.Sheaf.pullback A f).obj F ⟶ G)
    (b : (TopCat.Sheaf.pullback A g).obj G ⟶ H) :
    triangleMap A hp a ≫ triangleMap A hq b =
      triangleMap A (show r ≫ (g ≫ f) = p by
        rw [← Category.assoc, hq, hp])
        (TopCat.Sheaf.pullbackCompInv A g f F ≫
          (TopCat.Sheaf.pullback A g).map a ≫ b) := by
  subst p
  subst q
  change triangleMap A (rfl : (r ≫ g) ≫ f = (r ≫ g) ≫ f) a ≫
      triangleMap A (rfl : r ≫ g = r ≫ g) b =
    triangleMap A (rfl : r ≫ (g ≫ f) = (r ≫ g) ≫ f)
      (TopCat.Sheaf.pullbackCompInv A g f F ≫
        (TopCat.Sheaf.pullback A g).map a ≫ b)
  simpa [triangleMap, Category.assoc] using triangleMap_comp_aux A r g f a b

private theorem triangleMap_sheafMate_congr {W : TopCat.{w}}
    {X Y : SheafedSpace A} {p : W ⟶ (X : TopCat)} {q : W ⟶ (Y : TopCat)}
    (f g : Y ⟶ X) (h : f = g)
    (hf : q ≫ f.hom.base = p) (hg : q ≫ g.hom.base = p) :
    triangleMap A hf (sheafMate A f) = triangleMap A hg (sheafMate A g) := by
  cases h
  rfl

variable {J : Type wj} [Category.{vj} J]

/-- The sheaf at a stage, pulled back to the vertex of any cone of underlying spaces. -/
@[expose] def conePullbackObj (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (i : J) : c.pt.Sheaf A :=
  (TopCat.Sheaf.pullback A (c.π.app (op i))).obj (S.obj (op i)).sheaf

/-- The actual stage morphism, pulled across the corresponding cone triangle. -/
@[expose] def conePullbackMap (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) {i j : J} (a : i ⟶ j) :
    conePullbackObj A S c i ⟶ conePullbackObj A S c j :=
  triangleMap A (show c.π.app (op j) ≫ (S.map a.op).hom.base =
    c.π.app (op i) from c.w a.op) (sheafMate A (S.map a.op))

theorem conePullbackMap_id (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (i : J) :
    conePullbackMap A S c (𝟙 i) = 𝟙 (conePullbackObj A S c i) := by
  have hId : S.map ((𝟙 i).op) = 𝟙 (S.obj (op i)) := by
    simpa only [op_id] using S.map_id (op i)
  calc
    conePullbackMap A S c (𝟙 i) =
        triangleMap A (Category.comp_id (c.π.app (op i)))
          (sheafMate A (𝟙 (S.obj (op i)))) := by
      exact triangleMap_sheafMate_congr A
        (S.map ((𝟙 i).op)) (𝟙 (S.obj (op i))) hId (c.w (𝟙 i).op)
        (Category.comp_id (c.π.app (op i)))
    _ = _ := by
      rw [sheafMate_id]
      exact triangleMap_id A (c.π.app (op i)) (S.obj (op i)).sheaf

theorem conePullbackMap_comp (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) {i j k : J} (a : i ⟶ j) (b : j ⟶ k) :
    conePullbackMap A S c a ≫ conePullbackMap A S c b =
      conePullbackMap A S c (a ≫ b) := by
  have h := triangleMap_comp A
    (show c.π.app (op j) ≫ (S.map a.op).hom.base = c.π.app (op i) from c.w a.op)
    (show c.π.app (op k) ≫ (S.map b.op).hom.base = c.π.app (op j) from c.w b.op)
    (sheafMate A (S.map a.op)) (sheafMate A (S.map b.op))
  have hComp : S.map (a ≫ b).op = S.map b.op ≫ S.map a.op := by
    rw [op_comp, S.map_comp]
  have htransport := triangleMap_sheafMate_congr A
    (S.map (a ≫ b).op) (S.map b.op ≫ S.map a.op) hComp
    (show c.π.app (op k) ≫ (S.map (a ≫ b).op).hom.base =
      c.π.app (op i) from c.w (a ≫ b).op)
    (show c.π.app (op k) ≫ (S.map b.op ≫ S.map a.op).hom.base =
      c.π.app (op i) by
      change c.π.app (op k) ≫
        ((S.map b.op).hom.base ≫ (S.map a.op).hom.base) = _
      calc
        _ = (c.π.app (op k) ≫ (S.map b.op).hom.base) ≫
            (S.map a.op).hom.base := by rw [Category.assoc]
        _ = c.π.app (op j) ≫ (S.map a.op).hom.base :=
          congrArg (· ≫ (S.map a.op).hom.base) (c.w b.op)
        _ = c.π.app (op i) := c.w a.op)
  rw [sheafMate_comp] at htransport
  exact h.trans htransport.symm

/-- Pull a native contravariant sheafed-space diagram to any cone of its spaces. -/
@[expose] def conePullback (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) : J ⥤ c.pt.Sheaf A where
  obj := conePullbackObj A S c
  map := conePullbackMap A S c
  map_id := conePullbackMap_id A S c
  map_comp := fun a b ↦ (conePullbackMap_comp A S c a b).symm

@[simp] theorem conePullback_obj (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (i : J) :
    (conePullback A S c).obj i =
      (TopCat.Sheaf.pullback A (c.π.app (op i))).obj (S.obj (op i)).sheaf := rfl

@[simp] theorem conePullback_map (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) {i j : J} (a : i ⟶ j) :
    (conePullback A S c).map a =
      triangleMap A (show c.π.app (op j) ≫ (S.map a.op).hom.base =
        c.π.app (op i) from c.w a.op) (sheafMate A (S.map a.op)) := rfl

end AlgebraicGeometry.SheafedSpace
