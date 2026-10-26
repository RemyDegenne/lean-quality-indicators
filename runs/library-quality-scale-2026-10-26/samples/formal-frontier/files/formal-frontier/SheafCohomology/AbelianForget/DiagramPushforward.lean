/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SheafCohomology.AbelianForget.ConePullback
public import SheafCohomology.AbelianForget.SquareTransition
public import SheafCohomology.DiagramPushforward

public section

/-!
# Forgetting coefficients in native diagram pushforward

Forgetting additive structure commutes with direct image of actual native
sheafed-space diagrams, including the forward square transport on their arrows.
The same compatibility identifies native transported cones for arbitrary
continuous maps of vertices.
-/

set_option warningAsError true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open TopCat.Sheaf.AbelianForget

universe v vj wj

namespace AlgebraicGeometry.SheafedSpace.AbelianForget

variable {J : Type wj} [Category.{vj} J]

/-- The forgotten direct-image object is literally the Type-valued direct image. -/
theorem underlying_diagramPushforwardObj (X : SheafedSpace AddCommGrpCat.{v})
    {Y : TopCat.{v}} (f : (X : TopCat) ⟶ Y) :
    underlying.obj (SheafedSpace.diagramPushforwardObj AddCommGrpCat.{v} X f) =
      SheafedSpace.diagramPushforwardObj (Type v) (underlying.obj X) f := by
  rfl

/-- The actual arrow agrees after forgetting its additive structure; its
square equality transport is the accepted forward-square comparison. -/
theorem underlying_diagramPushforwardHom {Xj Xi : SheafedSpace AddCommGrpCat.{v}}
    {Yj Yi : TopCat.{v}} (r : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : (Xi : TopCat) ⟶ Yi) (fj : (Xj : TopCat) ⟶ Yj)
    (h : r.hom.base ≫ fi = fj ≫ q) :
    underlying.map (SheafedSpace.diagramPushforwardHom AddCommGrpCat.{v} r q fi fj h) =
      SheafedSpace.diagramPushforwardHom (Type v) (underlying.map r) q fi fj h := by
  apply InducedCategory.hom_ext
  apply PresheafedSpace.hext _ _ (by rfl)
  apply heq_of_eq
  have hsheaf : (underlyingSheaf Yi).map
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).map (⟨r.hom.c⟩ :
        Xi.sheaf ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{v} r.hom.base).obj Xj.sheaf) ≫
        (TopCat.Sheaf.SquareTransition.pushforwardSquareIso AddCommGrpCat.{v}
          r.hom.base q fi fj h).hom.app Xj.sheaf) =
    (TopCat.Sheaf.pushforward (Type v) fi).map
        ((underlyingSheaf Xi).map (⟨r.hom.c⟩ :
          Xi.sheaf ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{v} r.hom.base).obj Xj.sheaf)) ≫
      (TopCat.Sheaf.SquareTransition.pushforwardSquareIso (Type v)
        r.hom.base q fi fj h).hom.app ((underlyingSheaf Xj).obj Xj.sheaf)
      := by
    rw [(underlyingSheaf Yi).map_comp]
    erw [underlyingSheaf_pushforward_map]
    erw [underlyingSheaf_pushforwardSquareIso_hom_app]
  exact congrArg (fun m => m.hom) hsheaf

/-- Forgetting and native pushforward of an actual contravariant diagram
commute strictly. The same `f` is well-typed because `underlying_forget` is
a literal equality. -/
theorem underlying_diagramPushforward (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y) :
    SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f ⋙ underlying =
      SheafedSpace.diagramPushforward (Type v) (N ⋙ underlying) Y f := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j a
  exact underlying_diagramPushforwardHom (N.map a) (Y.map a)
    (f.app j) (f.app i) (SheafedSpace.diagramPushforward_square AddCommGrpCat.{v} N Y f a)

@[simp] theorem underlying_diagramPushforward_obj_carrier
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    (i : Jᵒᵖ) :
    ((underlying.obj ((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).obj i) :
      SheafedSpace (Type v)) : TopCat) = Y.obj i := rfl

@[simp] theorem underlying_diagramPushforward_obj_sheaf
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    (i : Jᵒᵖ) :
    (underlying.obj ((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).obj i)).sheaf =
      (TopCat.Sheaf.pushforward (Type v) (f.app i)).obj
        ((underlyingSheaf (N.obj i : TopCat)).obj (N.obj i).sheaf) := rfl

/-- The comparison at an actual stage arrow uses the already proved forward
square equality transport, rather than assuming an arrow-level comparison. -/
theorem underlying_diagramPushforward_map
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    {i j : Jᵒᵖ} (a : i ⟶ j) :
    underlying.map ((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map a) =
      (SheafedSpace.diagramPushforward (Type v) (N ⋙ underlying) Y f).map a :=
  underlying_diagramPushforwardHom (N.map a) (Y.map a)
    (f.app j) (f.app i) (SheafedSpace.diagramPushforward_square AddCommGrpCat.{v} N Y f a)

@[simp] theorem underlying_diagramPushforward_map_base
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    {i j : Jᵒᵖ} (a : i ⟶ j) :
    (underlying.map ((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map a)).hom.base =
      Y.map a := rfl

/-- The underlying sheaf map of the actual additive diagram arrow is direct
image of its actual additive stage map, followed by the Type-valued forward
square equality transport. -/
theorem underlying_diagramPushforward_map_sheafMap
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    {i j : Jᵒᵖ} (a : i ⟶ j) :
    (underlyingSheaf (Y.obj j)).map
      (⟨((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map a).hom.c⟩ :
        (TopCat.Sheaf.pushforward AddCommGrpCat.{v} (f.app j)).obj (N.obj j).sheaf ⟶
          (TopCat.Sheaf.pushforward AddCommGrpCat.{v} (Y.map a)).obj
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} (f.app i)).obj (N.obj i).sheaf)) =
      (TopCat.Sheaf.pushforward (Type v) (f.app j)).map
        ((underlyingSheaf (N.obj j : TopCat)).map (⟨(N.map a).hom.c⟩ :
          (N.obj j).sheaf ⟶
            (TopCat.Sheaf.pushforward AddCommGrpCat.{v} (N.map a).hom.base).obj
              (N.obj i).sheaf)) ≫
        (TopCat.Sheaf.SquareTransition.pushforwardSquareIso (Type v)
          (N.map a).hom.base (Y.map a) (f.app j) (f.app i)
          (SheafedSpace.diagramPushforward_square AddCommGrpCat.{v} N Y f a)).hom.app
            ((underlyingSheaf (N.obj i : TopCat)).obj (N.obj i).sheaf) := by
  rw [SheafedSpace.diagramPushforward_map_sheafMap AddCommGrpCat.{v} N Y f a,
    (underlyingSheaf (Y.obj j)).map_comp,
    underlyingSheaf_pushforward_map,
    underlyingSheaf_pushforwardSquareIso_hom_app]
  simp only [Functor.comp_obj, SheafedSpace.forget]

/-- The mate of the actual forgotten diagram arrow is the canonical mate
comparison at its target-space map. -/
theorem underlying_diagramPushforward_map_mate
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    {i j : Jᵒᵖ} (a : i ⟶ j) :
    SheafedSpace.sheafMate (Type v)
        (underlying.map ((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map a)) =
      canonicalComponent (Y.map a)
          ((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).obj j).sheaf ≫
        (underlyingSheaf (Y.obj i)).map
          (SheafedSpace.sheafMate AddCommGrpCat.{v}
            ((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map a)) :=
  underlying_sheafMate _

/-- The native forgotten cone and the Type-valued pushed cone agree after
postcomposition by the equality transport of the strict diagram equality.
The vertex comparison is the identity on the actual direct-image object. -/
@[expose] def underlying_diagramPushforwardConeIso
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) :
    (Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))).obj
        (underlying.mapCone
          (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h)) ≅
      SheafedSpace.diagramPushforwardCone (Type v) (N ⋙ underlying) Y f
        (underlying.mapCone c) d g h :=
  Cone.ext (Iso.refl _) (fun i => by
    simpa using
      (underlying_diagramPushforwardHom (c.π.app i) (d.π.app i)
        (f.app i) g (h i)))

@[simp] theorem underlying_diagramPushforwardCone_vertex
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) :
    ((Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))).obj
      (underlying.mapCone
        (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h))).pt =
      SheafedSpace.diagramPushforwardObj (Type v) (underlying.obj c.pt) g := rfl

@[simp] theorem underlying_diagramPushforwardCone_carrier
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) :
    (((Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))).obj
      (underlying.mapCone
        (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h))).pt :
      TopCat) = d.pt := rfl

@[simp] theorem underlying_diagramPushforwardCone_sheaf
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) :
    ((Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))).obj
      (underlying.mapCone
        (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h))).pt.sheaf =
      (TopCat.Sheaf.pushforward (Type v) g).obj
        ((underlyingSheaf (c.pt : TopCat)).obj c.pt.sheaf) := rfl

/-- Projection equality is along the native diagram equality transport,
not an artificially reconstructed cone. -/
theorem underlying_diagramPushforwardCone_projection
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i)
    (i : Jᵒᵖ) :
    ((Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))).obj
      (underlying.mapCone
        (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h))).π.app i =
      (SheafedSpace.diagramPushforwardCone (Type v) (N ⋙ underlying) Y f
        (underlying.mapCone c) d g h).π.app i := by
  simpa using underlying_diagramPushforwardHom
    (c.π.app i) (d.π.app i) (f.app i) g (h i)

@[simp] theorem underlying_diagramPushforwardCone_projection_base
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i)
    (i : Jᵒᵖ) :
    (((Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))).obj
      (underlying.mapCone
        (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h))).π.app i).hom.base =
      d.π.app i := by
  rw [underlying_diagramPushforwardCone_projection]
  rfl

/-- The vertex map of the canonical cone isomorphism is the identity. -/
@[simp] theorem underlying_diagramPushforwardConeIso_hom
    (N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : Jᵒᵖ ⥤ TopCat.{v}) (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) :
    (underlying_diagramPushforwardConeIso N Y f c d g h).hom.hom = 𝟙 _ := rfl

end AlgebraicGeometry.SheafedSpace.AbelianForget
