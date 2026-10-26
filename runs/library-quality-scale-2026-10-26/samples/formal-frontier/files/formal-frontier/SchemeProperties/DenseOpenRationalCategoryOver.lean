/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenRationalCategory
public import SchemeProperties.DenseOpenCompositionOver

@[expose] public section

/-!
# Dense-open rational maps over a fixed scheme

Objects have an arbitrary total structure morphism to the base. Arrows are native
quotient rational maps which pull dense opens back densely and admit an over-base
representative. In particular, the object structure maps need not pull dense
opens back densely.
-/

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme with a chosen total structure morphism to `S`. -/
structure DenseOpenRationalSchemeOver (S : Scheme.{u}) where
  toScheme : Scheme.{u}
  toBase : toScheme ⟶ S

namespace DenseOpenRationalSchemeOver

/-- Construct an object with an arbitrary total structure morphism. -/
def of {S X : Scheme.{u}} (p : X ⟶ S) : DenseOpenRationalSchemeOver S := ⟨X, p⟩

@[simp] theorem toScheme_of {S X : Scheme.{u}} (p : X ⟶ S) :
    (of p).toScheme = X := rfl

@[simp] theorem toBase_of {S X : Scheme.{u}} (p : X ⟶ S) :
    (of p).toBase = p := rfl

/-- An existing quotient rational map over `S` which pulls dense opens back densely.
The two explicit `Over` arguments retain distinct structure maps even if the
underlying schemes coincide. -/
structure Hom {S : Scheme.{u}} (X Y : DenseOpenRationalSchemeOver S) where
  toRationalMap : X.toScheme ⤏ Y.toScheme
  pullsDenseOpens : toRationalMap.PullsDenseOpens
  isOver : @Scheme.RationalMap.IsOver _ _ S
    (.ofHom X.toBase) (.ofHom Y.toBase) toRationalMap

/-- Bundle a native quotient rational map with its two required properties. -/
def hom {S : Scheme.{u}} {X Y : DenseOpenRationalSchemeOver S}
    (r : X.toScheme ⤏ Y.toScheme) (hr : r.PullsDenseOpens)
    (hS : @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Y.toBase) r) : Hom X Y := ⟨r, hr, hS⟩

@[simp] theorem toRationalMap_hom {S : Scheme.{u}}
    {X Y : DenseOpenRationalSchemeOver S} (r : X.toScheme ⤏ Y.toScheme)
    (hr : r.PullsDenseOpens)
    (hS : @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Y.toBase) r) :
    (hom r hr hS).toRationalMap = r := rfl

/-- The native existential over-base condition is equivalent to equality after
composing with the total target structure map. -/
theorem isOver_iff_compHom {S : Scheme.{u}} {X Y : DenseOpenRationalSchemeOver S}
    {r : X.toScheme ⤏ Y.toScheme} :
    @Scheme.RationalMap.IsOver _ _ S (.ofHom X.toBase) (.ofHom Y.toBase) r ↔
      r.compHom Y.toBase = X.toBase.toRationalMap :=
  @Scheme.RationalMap.isOver_iff _ _ S (.ofHom X.toBase) (.ofHom Y.toBase) r

/-- The over-base witness is exactly mathlib's native existential predicate. -/
theorem isOver_hom {S : Scheme.{u}} {X Y : DenseOpenRationalSchemeOver S}
    (r : X.toScheme ⤏ Y.toScheme) (hr : r.PullsDenseOpens)
    (hS : @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Y.toBase) r) :
    (hom r hr hS).isOver = hS := rfl

/-- An arrow is determined by its native quotient rational map. -/
@[ext] theorem hom_ext {S : Scheme.{u}} {X Y : DenseOpenRationalSchemeOver S}
    {f g : Hom X Y} (h : f.toRationalMap = g.toRationalMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Controlled composition and its existing unit, closure, relative and associativity
lemmas define a category over any base, without geometric hypotheses. -/
noncomputable instance {S : Scheme.{u}} : Category (DenseOpenRationalSchemeOver S) where
  Hom := Hom
  id X := by
    letI : X.toScheme.Over S := .ofHom X.toBase
    exact hom (Scheme.RationalMap.id X.toScheme)
      (Scheme.RationalMap.pullsDenseOpens_id X.toScheme) inferInstance
  comp {X Y Z} f g :=
    hom (f.toRationalMap.compOfPullsDenseOpens f.pullsDenseOpens g.toRationalMap)
      (f.toRationalMap.pullsDenseOpens_compOfPullsDenseOpens
        f.pullsDenseOpens g.toRationalMap g.pullsDenseOpens)
      (@Scheme.RationalMap.isOver_compOfPullsDenseOpens
        X.toScheme Y.toScheme Z.toScheme S
        (.ofHom X.toBase) (.ofHom Y.toBase) (.ofHom Z.toBase)
        f.toRationalMap f.pullsDenseOpens g.toRationalMap f.isOver g.isOver)
  id_comp f := by
    apply hom_ext
    exact Scheme.RationalMap.id_compOfPullsDenseOpens f.toRationalMap
  comp_id f := by
    apply hom_ext
    exact Scheme.RationalMap.compOfPullsDenseOpens_id f.toRationalMap f.pullsDenseOpens
  assoc f g h := by
    apply hom_ext
    exact Scheme.RationalMap.compOfPullsDenseOpens_assoc f.toRationalMap f.pullsDenseOpens
      g.toRationalMap g.pullsDenseOpens h.toRationalMap

@[simp] theorem toRationalMap_id {S : Scheme.{u}} (X : DenseOpenRationalSchemeOver S) :
    (𝟙 X : X ⟶ X).toRationalMap = Scheme.RationalMap.id X.toScheme := rfl

@[simp] theorem toRationalMap_comp {S : Scheme.{u}}
    {X Y Z : DenseOpenRationalSchemeOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap =
      f.toRationalMap.compOfPullsDenseOpens f.pullsDenseOpens g.toRationalMap := rfl

/-- Forget the chosen structure maps and the over-base condition, retaining the
native quotient rational map and its dense-open pullback property. -/
def forget (S : Scheme.{u}) : DenseOpenRationalSchemeOver S ⥤ DenseOpenRationalScheme.{u} where
  obj X := DenseOpenRationalScheme.of X.toScheme
  map f := DenseOpenRationalScheme.hom f.toRationalMap f.pullsDenseOpens
  map_id _ := DenseOpenRationalScheme.hom_ext rfl
  map_comp _ _ := DenseOpenRationalScheme.hom_ext rfl

@[simp] theorem forget_obj_toScheme {S : Scheme.{u}} (X : DenseOpenRationalSchemeOver S) :
    ((forget S).obj X).toScheme = X.toScheme := rfl

@[simp] theorem forget_map_toRationalMap {S : Scheme.{u}}
    {X Y : DenseOpenRationalSchemeOver S} (f : X ⟶ Y) :
    ((forget S).map f).toRationalMap = f.toRationalMap := rfl

/-- The forgetful functor is faithful, but is not asserted to be full. -/
instance {S : Scheme.{u}} : (forget S).Faithful where
  map_injective := fun {_ _} _ _ h =>
    hom_ext (congrArg DenseOpenRationalScheme.Hom.toRationalMap h)

end DenseOpenRationalSchemeOver
end AlgebraicGeometry
