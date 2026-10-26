/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Restriction maps and intersections of open ringed subspaces

The canonical restrictions of a ringed space to two opens intersect in a categorical
pullback. All maps and equalities are full ringed-space morphisms, including the
maps of structure sheaves. The construction uses the open-immersion lifting property
for presheafed spaces and introduces no local-ring assumptions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}} (U V : Opens X)

private theorem range_subset_ofRestrict {T : RingedSpace.{u, u}} (g : T ⟶ X)
    (h : ∀ t : T, g.hom.base t ∈ U) :
    Set.range g.hom.base ⊆ Set.range (X.ofRestrict U.isOpenEmbedding).hom.base := by
  rintro _ ⟨t, rfl⟩
  exact ⟨⟨g.hom.base t, h t⟩, rfl⟩

private noncomputable def liftToRestrict {T : RingedSpace.{u, u}} (g : T ⟶ X)
    (h : ∀ t : T, g.hom.base t ∈ U) : T ⟶ X.restrict U.isOpenEmbedding := by
  apply InducedCategory.homMk
  exact PresheafedSpace.IsOpenImmersion.lift (X.ofRestrict U.isOpenEmbedding).hom g.hom
    (range_subset_ofRestrict U g h)

@[reassoc]
private theorem liftToRestrict_fac {T : RingedSpace.{u, u}} (g : T ⟶ X)
    (h : ∀ t : T, g.hom.base t ∈ U) :
    liftToRestrict U g h ≫ X.ofRestrict U.isOpenEmbedding = g := by
  apply InducedCategory.hom_ext
  exact PresheafedSpace.IsOpenImmersion.lift_fac
    (X.ofRestrict U.isOpenEmbedding).hom g.hom (range_subset_ofRestrict U g h)

/-- The canonical full morphism from a smaller open restriction to a larger one. -/
noncomputable def restrictMap (h : U ≤ V) :
    X.restrict U.isOpenEmbedding ⟶ X.restrict V.isOpenEmbedding := by
  apply InducedCategory.homMk
  exact PresheafedSpace.IsOpenImmersion.lift (X.ofRestrict V.isOpenEmbedding).hom
    (X.ofRestrict U.isOpenEmbedding).hom
    (by
      exact range_subset_ofRestrict V (X.ofRestrict U.isOpenEmbedding) (fun t => h t.property))

private theorem restrictMap_eq_liftToRestrict (h : U ≤ V) :
    restrictMap U V h =
      liftToRestrict V (X.ofRestrict U.isOpenEmbedding) (fun t => h t.property) := rfl

/-- The restriction map factors the original full open inclusion. -/
@[reassoc (attr := simp)]
theorem restrictMap_ofRestrict (h : U ≤ V) :
    restrictMap U V h ≫ X.ofRestrict V.isOpenEmbedding =
      X.ofRestrict U.isOpenEmbedding :=
  liftToRestrict_fac V (X.ofRestrict U.isOpenEmbedding) (fun t => h t.property)

/-- On points, the restriction map is the canonical inclusion of subtypes. -/
@[simp]
theorem restrictMap_base (h : U ≤ V) (t : U) :
    (restrictMap U V h).hom.base t = ⟨t.1, h t.2⟩ := by
  apply Subtype.ext
  have heq := congrArg (fun f : X.restrict U.isOpenEmbedding ⟶ X => f.hom.base t)
    (restrictMap_ofRestrict U V h)
  exact heq

/-- Two successive restrictions compose to the direct restriction. -/
@[reassoc]
theorem restrictMap_comp {W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W) :
    restrictMap U V hUV ≫ restrictMap V W hVW =
      restrictMap U W (hUV.trans hVW) := by
  rw [← cancel_mono (X.ofRestrict W.isOpenEmbedding)]
  simp only [Category.assoc, restrictMap_ofRestrict]

/-- Restricting to the same open is the identity full morphism. -/
@[simp]
theorem restrictMap_id : restrictMap U U le_rfl = 𝟙 _ := by
  rw [← cancel_mono (X.ofRestrict U.isOpenEmbedding)]
  simp only [restrictMap_ofRestrict, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The literal intersection restriction is the full categorical pullback of the two
canonical inclusions. This also holds for empty or non-covering opens. -/
theorem isPullback_restrictInf :
    IsPullback
      (restrictMap (U ⊓ V) U inf_le_left)
      (restrictMap (U ⊓ V) V inf_le_right)
      (X.ofRestrict U.isOpenEmbedding)
      (X.ofRestrict V.isOpenEmbedding) := by
  let left := restrictMap (U ⊓ V) U inf_le_left
  let right := restrictMap (U ⊓ V) V inf_le_right
  have comm : left ≫ X.ofRestrict U.isOpenEmbedding =
      right ≫ X.ofRestrict V.isOpenEmbedding := by
    simp only [left, right, restrictMap_ofRestrict]
  refine { w := comm, isLimit' := ⟨PullbackCone.isLimitAux'
      (PullbackCone.mk left right comm) ?_⟩ }
  intro s
  let common : s.pt ⟶ X := s.fst ≫ X.ofRestrict U.isOpenEmbedding
  have hmem : ∀ t : s.pt, common.hom.base t ∈ U ⊓ V := by
    intro t
    constructor
    · exact (s.fst.hom.base t).property
    · have hs := congrArg (fun f : s.pt ⟶ X => f.hom.base t) s.condition
      change (s.fst.hom.base t).1 = (s.snd.hom.base t).1 at hs
      change (s.fst.hom.base t).1 ∈ V
      rw [hs]
      exact (s.snd.hom.base t).property
  let l := liftToRestrict (U ⊓ V) common hmem
  have hl : l ≫ X.ofRestrict (U ⊓ V).isOpenEmbedding = common :=
    liftToRestrict_fac _ _ _
  refine ⟨l, ?_, ?_, ?_⟩
  · change l ≫ left = s.fst
    rw [← cancel_mono (X.ofRestrict U.isOpenEmbedding), Category.assoc,
      show left ≫ X.ofRestrict U.isOpenEmbedding =
        X.ofRestrict (U ⊓ V).isOpenEmbedding from restrictMap_ofRestrict _ _ _]
    exact hl
  · change l ≫ right = s.snd
    rw [← cancel_mono (X.ofRestrict V.isOpenEmbedding), Category.assoc,
      show right ≫ X.ofRestrict V.isOpenEmbedding =
        X.ofRestrict (U ⊓ V).isOpenEmbedding from restrictMap_ofRestrict _ _ _]
    exact hl.trans s.condition
  · intro m hm _
    change m ≫ left = s.fst at hm
    rw [← cancel_mono (X.ofRestrict (U ⊓ V).isOpenEmbedding)]
    calc
      m ≫ X.ofRestrict (U ⊓ V).isOpenEmbedding =
          (m ≫ left) ≫ X.ofRestrict U.isOpenEmbedding := by
            rw [Category.assoc, restrictMap_ofRestrict]
      _ = common := by rw [hm]
      _ = l ≫ X.ofRestrict (U ⊓ V).isOpenEmbedding := hl.symm

end AlgebraicGeometry.RingedSpace
