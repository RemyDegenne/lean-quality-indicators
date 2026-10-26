/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing a partial map with a morphism on an open

A partial map and a morphism on an open subscheme whose morphisms agree on the intersection
glue to a partial map on the union. The added open need not be dense: density of the union
follows from the domain of the partial map. Gluing two partial maps is the corresponding
special case. The construction uses `Scheme.Cover.mkOfCovers` and `Scheme.Cover.glueMorphisms`;
it does not require reducedness or separatedness.

## Implementation notes

The domain is the supremum of the given domain and open, rather than a maximal domain of a
rational map. A local two-element open cover supplies the morphism. The intersection
compatibility is transported to the cover pullbacks using `isPullback_opens_inf_le`.

## References

* Mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`,
  `AlgebraicGeometry/Birational/RationalMap.lean`: the partial-map carrier, restrictions and
  rational-map quotient; its `RationalMap.toPartialMap` also uses the intersection-to-pullback
  transport for cover gluing.
* Mathlib at the same revision, `AlgebraicGeometry/Cover/MorphismProperty.lean`,
  `AlgebraicGeometry/Restrict.lean` and `AlgebraicGeometry/Gluing.lean`: the cover constructor,
  open-intersection pullback squares and gluing of scheme morphisms.
* Mathlib at the same revision, `AlgebraicGeometry/Over.lean` and
  `CategoryTheory/Comma/Over/OverClass.lean`: structure morphisms and morphisms over a base.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.PartialMap

variable {X Y S : Scheme.{u}}

/-- Glue a partial map with a morphism on an open that agrees on their intersection. -/
noncomputable def glueHom (p : X.PartialMap Y) (V : X.Opens) (f : V.toScheme ⟶ Y)
    (h : X.homOfLE (inf_le_left : p.domain ⊓ V ≤ p.domain) ≫ p.hom =
      X.homOfLE (inf_le_right : p.domain ⊓ V ≤ V) ≫ f) :
    X.PartialMap Y where
  domain := p.domain ⊔ V
  dense_domain := p.dense_domain.mono
    (show (p.domain : Set X) ⊆ ((p.domain ⊔ V : X.Opens) : Set X) from le_sup_left)
  hom := by
    let C : (p.domain ⊔ V).toScheme.OpenCover :=
      Cover.mkOfCovers Bool
        (fun b ↦ match b with
          | false => V.toScheme
          | true => p.domain.toScheme)
        (fun b ↦ by
          cases b with
          | false => exact X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V)
          | true => exact X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V))
        (by
          intro x
          rcases x.2 with hx | hx
          · refine ⟨true, ⟨x.1, hx⟩, ?_⟩
            apply Subtype.ext
            exact Scheme.homOfLE_apply _ _
          · refine ⟨false, ⟨x.1, hx⟩, ?_⟩
            apply Subtype.ext
            exact Scheme.homOfLE_apply _ _)
        (by
          intro b
          cases b <;> infer_instance)
    let k : ∀ b : Bool, C.X b ⟶ Y := fun b ↦ by
      cases b with
      | false => exact f
      | true => exact p.hom
    refine C.glueMorphisms k ?_
    change ∀ b c : Bool, pullback.fst (C.f b) (C.f c) ≫ k b =
      pullback.snd (C.f b) (C.f c) ≫ k c
    intro b c
    cases b <;> cases c
    · change pullback.fst (X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V))
          (X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V)) ≫ f =
        pullback.snd (X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V))
          (X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V)) ≫ f
      refine (cancel_epi (isPullback_opens_inf_le
        (le_sup_right : V ≤ p.domain ⊔ V)
        (le_sup_right : V ≤ p.domain ⊔ V)).isoPullback.hom).mp ?_
      -- The two inclusion proofs into the repeated open agree by proof irrelevance.
      simp only [IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc]
    · change pullback.fst (X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V))
          (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V)) ≫ f =
        pullback.snd (X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V))
          (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V)) ≫ p.hom
      -- Flipping the square keeps the same intersection scheme.
      refine (cancel_epi (isPullback_opens_inf_le
        (le_sup_left : p.domain ≤ p.domain ⊔ V)
        (le_sup_right : V ≤ p.domain ⊔ V)).flip.isoPullback.hom).mp ?_
      simpa only [IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc] using h.symm
    · change pullback.fst (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V))
          (X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V)) ≫ p.hom =
        pullback.snd (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V))
          (X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V)) ≫ f
      refine (cancel_epi (isPullback_opens_inf_le
        (le_sup_left : p.domain ≤ p.domain ⊔ V)
        (le_sup_right : V ≤ p.domain ⊔ V)).isoPullback.hom).mp ?_
      simpa only [IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc] using h
    · change pullback.fst (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V))
          (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V)) ≫ p.hom =
        pullback.snd (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V))
          (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V)) ≫ p.hom
      refine (cancel_epi (isPullback_opens_inf_le
        (le_sup_left : p.domain ≤ p.domain ⊔ V)
        (le_sup_left : p.domain ≤ p.domain ⊔ V)).isoPullback.hom).mp ?_
      simp only [IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc]

/-- Glue two partial maps whose morphisms agree on the intersection of their domains.

This is `glueHom` applied to the second partial map's domain and morphism. -/
noncomputable def glue (p q : X.PartialMap Y)
    (h : X.homOfLE (inf_le_left : p.domain ⊓ q.domain ≤ p.domain) ≫ p.hom =
      X.homOfLE (inf_le_right : p.domain ⊓ q.domain ≤ q.domain) ≫ q.hom) :
    X.PartialMap Y :=
  p.glueHom q.domain q.hom h

private lemma hom_ext_sup (U V : X.Opens) (g₁ g₂ : (U ⊔ V).toScheme ⟶ Y)
    (hU : X.homOfLE (le_sup_left : U ≤ U ⊔ V) ≫ g₁ =
      X.homOfLE (le_sup_left : U ≤ U ⊔ V) ≫ g₂)
    (hV : X.homOfLE (le_sup_right : V ≤ U ⊔ V) ≫ g₁ =
      X.homOfLE (le_sup_right : V ≤ U ⊔ V) ≫ g₂) : g₁ = g₂ := by
  let C : (U ⊔ V).toScheme.OpenCover :=
    Cover.mkOfCovers Bool
      (fun b ↦ match b with
        | false => V.toScheme
        | true => U.toScheme)
      (fun b ↦ by
        cases b with
        | false => exact X.homOfLE (le_sup_right : V ≤ U ⊔ V)
        | true => exact X.homOfLE (le_sup_left : U ≤ U ⊔ V))
      (by
        intro x
        rcases x.2 with hx | hx
        · refine ⟨true, ⟨x.1, hx⟩, ?_⟩
          apply Subtype.ext
          exact Scheme.homOfLE_apply _ _
        · refine ⟨false, ⟨x.1, hx⟩, ?_⟩
          apply Subtype.ext
          exact Scheme.homOfLE_apply _ _)
      (by
        intro b
        cases b <;> infer_instance)
  refine C.hom_ext g₁ g₂ ?_
  intro b
  cases b with
  | false => exact hV
  | true => exact hU

section GlueHom

variable (p : X.PartialMap Y) (V : X.Opens) (f : V.toScheme ⟶ Y)
  (h : X.homOfLE (inf_le_left : p.domain ⊓ V ≤ p.domain) ≫ p.hom =
    X.homOfLE (inf_le_right : p.domain ⊓ V ≤ V) ≫ f)

/-- The domain of the gluing is the union of the original domain and the added open. -/
@[simp]
lemma glueHom_domain : (p.glueHom V f h).domain = p.domain ⊔ V := rfl

/-- The glued morphism restricts to the original morphism on its whole domain. -/
@[reassoc (attr := simp)]
lemma homOfLE_glueHom_left :
    X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V) ≫ (p.glueHom V f h).hom = p.hom := by
  dsimp (config := { zeta := false }) only [glueHom]
  extract_lets C k
  exact Cover.ι_glueMorphisms C k _ true

/-- The glued morphism restricts to the given morphism on the whole added open. -/
@[reassoc (attr := simp)]
lemma homOfLE_glueHom_right :
    X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V) ≫ (p.glueHom V f h).hom = f := by
  dsimp (config := { zeta := false }) only [glueHom]
  extract_lets C k
  exact Cover.ι_glueMorphisms C k _ false

/-- Restricting the gluing to the entire original domain recovers the partial map. -/
@[simp]
lemma glueHom_restrict_left :
    (p.glueHom V f h).restrict p.domain p.dense_domain
      (le_sup_left : p.domain ≤ p.domain ⊔ V) = p := by
  refine PartialMap.ext _ _ rfl ?_
  calc
    _ = X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V) ≫
        (p.glueHom V f h).hom := rfl
    _ = p.hom := homOfLE_glueHom_left p V f h
    _ = (X.isoOfEq (rfl : p.domain = p.domain)).hom ≫ p.hom := by
      rw [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp]

/-- A morphism on the union is the glued morphism exactly when it has both given restrictions. -/
lemma glueHom_hom_eq_iff (g : (p.domain ⊔ V).toScheme ⟶ Y) :
    (p.glueHom V f h).hom = g ↔
      (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V) ≫ g = p.hom ∧
        X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V) ≫ g = f) := by
  constructor
  · rintro rfl
    exact ⟨homOfLE_glueHom_left p V f h, homOfLE_glueHom_right p V f h⟩
  · rintro ⟨hleft, hright⟩
    apply hom_ext_sup p.domain V
    · exact (homOfLE_glueHom_left p V f h).trans hleft.symm
    · exact (homOfLE_glueHom_right p V f h).trans hright.symm

/-- The gluing represents the same rational map as the original partial map. -/
@[simp]
lemma glueHom_toRationalMap : (p.glueHom V f h).toRationalMap = p.toRationalMap := by
  exact (restrict_toRationalMap (p.glueHom V f h) p.domain p.dense_domain
    (le_sup_left : p.domain ≤ p.domain ⊔ V)).symm.trans
      (congrArg (fun q : X.PartialMap Y ↦ q.toRationalMap) (glueHom_restrict_left p V f h))

/-- Gluing a partial map and a morphism over the same base preserves
the structure over that base. -/
instance isOver_glueHom [X.Over S] [Y.Over S] [p.IsOver S] [f.IsOver S] :
    (p.glueHom V f h).IsOver S := by
  apply (isOver_iff (S := S) (f := p.glueHom V f h)).mpr
  change (p.glueHom V f h).hom ≫ (Y ↘ S) = (p.domain ⊔ V).ι ≫ (X ↘ S)
  apply hom_ext_sup p.domain V
  · calc
      X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V) ≫
          ((p.glueHom V f h).hom ≫ (Y ↘ S)) =
          (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V) ≫
            (p.glueHom V f h).hom) ≫ (Y ↘ S) := (Category.assoc _ _ _).symm
      _ = p.hom ≫ (Y ↘ S) :=
        congrArg (fun g : p.domain.toScheme ⟶ Y ↦ g ≫ (Y ↘ S))
          (homOfLE_glueHom_left p V f h)
      _ = p.domain.ι ≫ (X ↘ S) := by
        exact (comp_over p.hom S).trans (Scheme.Opens.ι_comp_over p.domain S).symm
      _ = (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V) ≫
          (p.domain ⊔ V).ι) ≫ (X ↘ S) :=
        congrArg (fun g : p.domain.toScheme ⟶ X ↦ g ≫ (X ↘ S))
          (Scheme.homOfLE_ι X (le_sup_left : p.domain ≤ p.domain ⊔ V)).symm
      _ = X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ V) ≫
          ((p.domain ⊔ V).ι ≫ (X ↘ S)) := Category.assoc _ _ _
  · calc
      X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V) ≫
          ((p.glueHom V f h).hom ≫ (Y ↘ S)) =
          (X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V) ≫
            (p.glueHom V f h).hom) ≫ (Y ↘ S) := (Category.assoc _ _ _).symm
      _ = f ≫ (Y ↘ S) :=
        congrArg (fun g : V.toScheme ⟶ Y ↦ g ≫ (Y ↘ S))
          (homOfLE_glueHom_right p V f h)
      _ = V.toScheme ↘ S := comp_over f S
      _ = V.ι ≫ (X ↘ S) := (Scheme.Opens.ι_comp_over V S).symm
      _ = (X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V) ≫
          (p.domain ⊔ V).ι) ≫ (X ↘ S) :=
        congrArg (fun g : V.toScheme ⟶ X ↦ g ≫ (X ↘ S))
          (Scheme.homOfLE_ι X (le_sup_right : V ≤ p.domain ⊔ V)).symm
      _ = X.homOfLE (le_sup_right : V ≤ p.domain ⊔ V) ≫
          ((p.domain ⊔ V).ι ≫ (X ↘ S)) := Category.assoc _ _ _

end GlueHom

variable (p q : X.PartialMap Y)
  (h : X.homOfLE (inf_le_left : p.domain ⊓ q.domain ≤ p.domain) ≫ p.hom =
    X.homOfLE (inf_le_right : p.domain ⊓ q.domain ≤ q.domain) ≫ q.hom)

/-- The domain of a gluing is the union of the two domains. -/
@[simp]
lemma glue_domain : (p.glue q h).domain = p.domain ⊔ q.domain := rfl

/-- The glued morphism restricts to the first morphism on its whole domain. -/
@[reassoc (attr := simp)]
lemma homOfLE_glue_left :
    X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ q.domain) ≫ (p.glue q h).hom = p.hom := by
  exact homOfLE_glueHom_left p q.domain q.hom h

/-- The glued morphism restricts to the second morphism on its whole domain. -/
@[reassoc (attr := simp)]
lemma homOfLE_glue_right :
    X.homOfLE (le_sup_right : q.domain ≤ p.domain ⊔ q.domain) ≫ (p.glue q h).hom = q.hom := by
  exact homOfLE_glueHom_right p q.domain q.hom h

/-- Restricting the gluing to the entire first domain recovers the first partial map. -/
@[simp]
lemma glue_restrict_left :
    (p.glue q h).restrict p.domain p.dense_domain
      (le_sup_left : p.domain ≤ p.domain ⊔ q.domain) = p := by
  exact glueHom_restrict_left p q.domain q.hom h

/-- Restricting the gluing to the entire second domain recovers the second partial map. -/
@[simp]
lemma glue_restrict_right :
    (p.glue q h).restrict q.domain q.dense_domain
      (le_sup_right : q.domain ≤ p.domain ⊔ q.domain) = q := by
  refine PartialMap.ext _ _ rfl ?_
  calc
    _ = X.homOfLE (le_sup_right : q.domain ≤ p.domain ⊔ q.domain) ≫
        (p.glue q h).hom := rfl
    _ = q.hom := homOfLE_glue_right p q h
    _ = (X.isoOfEq (rfl : q.domain = q.domain)).hom ≫ q.hom := by
      rw [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp]

/-- A morphism on the union is the glued morphism exactly when it has both given restrictions. -/
lemma glue_hom_eq_iff (g : (p.domain ⊔ q.domain).toScheme ⟶ Y) :
    (p.glue q h).hom = g ↔
      (X.homOfLE (le_sup_left : p.domain ≤ p.domain ⊔ q.domain) ≫ g = p.hom ∧
        X.homOfLE (le_sup_right : q.domain ≤ p.domain ⊔ q.domain) ≫ g = q.hom) := by
  exact glueHom_hom_eq_iff p q.domain q.hom h g

/-- The gluing represents the same rational map as the first partial map. -/
@[simp]
lemma glue_toRationalMap : (p.glue q h).toRationalMap = p.toRationalMap := by
  exact glueHom_toRationalMap p q.domain q.hom h

/-- The gluing also represents the same rational map as the second partial map. -/
lemma glue_toRationalMap_right : (p.glue q h).toRationalMap = q.toRationalMap := by
  calc
    (p.glue q h).toRationalMap =
        ((p.glue q h).restrict q.domain q.dense_domain
          (le_sup_right : q.domain ≤ p.domain ⊔ q.domain)).toRationalMap :=
      (restrict_toRationalMap (p.glue q h) q.domain q.dense_domain le_sup_right).symm
    _ = q.toRationalMap := congrArg toRationalMap (glue_restrict_right p q h)

/-- Gluing two partial maps over the same base preserves their structure over that base. -/
instance isOver_glue [X.Over S] [Y.Over S] [p.IsOver S] [q.IsOver S] :
    (p.glue q h).IsOver S := by
  exact isOver_glueHom (S := S) p q.domain q.hom h

end AlgebraicGeometry.Scheme.PartialMap
