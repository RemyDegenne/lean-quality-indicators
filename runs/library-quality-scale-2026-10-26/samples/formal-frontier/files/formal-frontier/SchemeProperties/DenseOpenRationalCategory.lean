/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenCompositionAssociativity
public import SchemeProperties.DenseOpenCompositionUnits
public import SchemeProperties.DenseOpenPullbackDominance

@[expose] public section

/-!
# The category of rational maps pulling back dense opens densely

Objects are arbitrary schemes in one universe. Arrows are mathlib's native quotient
rational maps with the existing `RationalMap.PullsDenseOpens` property; no new
equivalence of partial maps or geometric condition on objects is introduced.
-/

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme viewed as an object of the dense-open rational-map category. -/
structure DenseOpenRationalScheme where
  toScheme : Scheme.{u}

namespace DenseOpenRationalScheme

/-- Regard an arbitrary scheme as an object of the dense-open rational-map category. -/
def of (X : Scheme.{u}) : DenseOpenRationalScheme.{u} := ⟨X⟩

/-- A native rational map whose inverse image of every dense open is dense. -/
structure Hom (X Y : DenseOpenRationalScheme.{u}) where
  toRationalMap : X.toScheme ⤏ Y.toScheme
  pullsDenseOpens : toRationalMap.PullsDenseOpens

/-- Construct an arrow from a native rational map and its dense-open pullback property. -/
def hom {X Y : DenseOpenRationalScheme.{u}} (r : X.toScheme ⤏ Y.toScheme)
    (hr : r.PullsDenseOpens) : Hom X Y := ⟨r, hr⟩

@[simp] theorem toRationalMap_hom {X Y : DenseOpenRationalScheme.{u}}
    (r : X.toScheme ⤏ Y.toScheme) (hr : r.PullsDenseOpens) :
    (hom r hr).toRationalMap = r := rfl

/-- Two arrows with equal underlying quotient rational maps are equal. -/
@[ext] theorem hom_ext {X Y : DenseOpenRationalScheme.{u}} {f g : Hom X Y}
    (h : f.toRationalMap = g.toRationalMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Controlled composition makes dense-open rational maps into a category. -/
noncomputable instance : Category DenseOpenRationalScheme.{u} where
  Hom := Hom
  id X := hom (Scheme.RationalMap.id X.toScheme)
    (Scheme.RationalMap.pullsDenseOpens_id X.toScheme)
  comp f g := hom (f.toRationalMap.compOfPullsDenseOpens f.pullsDenseOpens g.toRationalMap)
    (f.toRationalMap.pullsDenseOpens_compOfPullsDenseOpens
      f.pullsDenseOpens g.toRationalMap g.pullsDenseOpens)
  id_comp f := hom_ext (Scheme.RationalMap.id_compOfPullsDenseOpens f.toRationalMap)
  comp_id f := hom_ext
    (Scheme.RationalMap.compOfPullsDenseOpens_id f.toRationalMap f.pullsDenseOpens)
  assoc f g h := hom_ext
    (Scheme.RationalMap.compOfPullsDenseOpens_assoc f.toRationalMap f.pullsDenseOpens
      g.toRationalMap g.pullsDenseOpens h.toRationalMap)

@[simp] theorem toRationalMap_id (X : DenseOpenRationalScheme.{u}) :
    (𝟙 X : X ⟶ X).toRationalMap = Scheme.RationalMap.id X.toScheme := rfl

@[simp] theorem toRationalMap_comp {X Y Z : DenseOpenRationalScheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap =
      f.toRationalMap.compOfPullsDenseOpens f.pullsDenseOpens g.toRationalMap := rfl

/-- With nonempty preirreducible source and target, the arrow predicate is
equivalent to native rational-map dominance. No such equivalence is claimed
for arbitrary schemes. -/
def homEquivDominant (X Y : DenseOpenRationalScheme.{u})
    [PreirreducibleSpace X.toScheme] [Nonempty X.toScheme]
    [PreirreducibleSpace Y.toScheme] [Nonempty Y.toScheme] :
    (X ⟶ Y) ≃ {r : X.toScheme ⤏ Y.toScheme // r.IsDominant} where
  toFun f := ⟨f.toRationalMap,
    (Scheme.RationalMap.pullsDenseOpens_iff_isDominant f.toRationalMap).mp
      f.pullsDenseOpens⟩
  invFun r := hom r.1
    ((Scheme.RationalMap.pullsDenseOpens_iff_isDominant r.1).mpr r.2)
  left_inv f := by
    cases f
    rfl
  right_inv r := by
    cases r
    rfl

@[simp] theorem homEquivDominant_apply_val (X Y : DenseOpenRationalScheme.{u})
    [PreirreducibleSpace X.toScheme] [Nonempty X.toScheme]
    [PreirreducibleSpace Y.toScheme] [Nonempty Y.toScheme] (f : X ⟶ Y) :
    (homEquivDominant X Y f).1 = f.toRationalMap := rfl

end DenseOpenRationalScheme
end AlgebraicGeometry
