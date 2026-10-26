/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenComposition

@[expose] public section

/-!
# Units for dense-open-controlled composition

The identity partial and rational maps pull back dense opens densely. The left
unit laws impose no predicate on the second map; the right unit laws use only
the existing predicate on the first map.

## References

- [Mathlib, `AlgebraicGeometry/Birational/Composition.lean`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/Composition.lean#L138-L146):
  Justus Springer's native partial-composition normalization is adapted to
  controlled composition; the predicate and unit laws here have their own proofs.
- [Mathlib, `AlgebraicGeometry/Birational/RationalMap.lean`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/RationalMap.lean#L137-L155):
  Andrew Yang's `Scheme.PartialMap.id` is an imported API; the rational-map
  [quotient and identity](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/RationalMap.lean#L374-L395)
  are likewise used rather than redefined here.
-/

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

namespace PartialMap

/-- The identity pulls back dense opens in the ambient source scheme. -/
theorem pullsDenseOpens_id (X : Scheme.{u}) : (PartialMap.id X).PullsDenseOpens := by
  apply pullsDenseOpens_of_isOpenMap
  change IsOpenMap (X.topIso.hom ≫ 𝟙 X)
  simpa only [Category.comp_id, topIso_hom] using
    ((⊤ : X.Opens).ι).isOpenEmbedding.isOpenMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Literal left identity on arbitrary partial maps, without a predicate on the second map. -/
theorem id_compOfPullsDenseOpens (f : X.PartialMap Y) :
    (PartialMap.id X).compOfPullsDenseOpens (pullsDenseOpens_id X) f = f := by
  ext1
  · simp_rw [compOfPullsDenseOpens_domain, Hom.toPartialMap_domain, Hom.toPartialMap_hom,
      Category.comp_id, ← X.topIso_hom, ← Hom.inv_image, ← Hom.comp_image,
      Iso.inv_hom_id, Hom.id_image]
  · simp_rw [compOfPullsDenseOpens_hom, Hom.toPartialMap_hom, Hom.toPartialMap_domain,
      morphismRestrict_comp, morphismRestrict_id, ← X.topIso_hom,
      Hom.comp_preimage, Hom.id_preimage, Category.comp_id,
      ← X.topIso.hom.isoImage_preimage_hom_homOfLE, Category.assoc,
      Iso.inv_hom_id_assoc]
    rfl

/-- Literal right identity, requiring the existing predicate on the first map. -/
theorem compOfPullsDenseOpens_id (f : X.PartialMap Y) (hf : f.PullsDenseOpens) :
    f.compOfPullsDenseOpens hf (PartialMap.id Y) = f := by
  change f.compOfPullsDenseOpens hf (𝟙 Y : Y ⟶ Y).toPartialMap = f
  rw [compOfPullsDenseOpens_toPartialMap, compHom_id]

end PartialMap

namespace RationalMap

/-- The quotient identity pulls back dense opens in the ambient source scheme. -/
theorem pullsDenseOpens_id (X : Scheme.{u}) : (RationalMap.id X).PullsDenseOpens :=
  (PartialMap.id X).pullsDenseOpens_toRationalMap_iff.mpr (PartialMap.pullsDenseOpens_id X)

/-- Left identity in the native rational-map quotient, for any second map. -/
theorem id_compOfPullsDenseOpens (r : X ⤏ Y) :
    (RationalMap.id X).compOfPullsDenseOpens (pullsDenseOpens_id X) r = r := by
  obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective r
  change (PartialMap.id X).toRationalMap.compOfPullsDenseOpens
    ((PartialMap.id X).pullsDenseOpens_toRationalMap_iff.mpr
      (PartialMap.pullsDenseOpens_id X)) f.toRationalMap = f.toRationalMap
  rw [toRationalMap_compOfPullsDenseOpens (hf := PartialMap.pullsDenseOpens_id X),
    PartialMap.id_compOfPullsDenseOpens]

/-- Right identity in the native rational-map quotient, with the first-map predicate. -/
theorem compOfPullsDenseOpens_id (r : X ⤏ Y) (hr : r.PullsDenseOpens) :
    r.compOfPullsDenseOpens hr (RationalMap.id Y) = r := by
  change r.compOfPullsDenseOpens hr (𝟙 Y : Y ⟶ Y).toRationalMap = r
  rw [compOfPullsDenseOpens_toRationalMap]
  obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective r
  rw [← compHom_toRationalMap, PartialMap.compHom_id]

end RationalMap

end AlgebraicGeometry.Scheme
