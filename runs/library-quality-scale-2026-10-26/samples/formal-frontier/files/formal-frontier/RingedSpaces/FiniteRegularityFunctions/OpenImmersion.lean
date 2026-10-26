/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces.FiniteRegularityFunctions.Maps
public import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Finite-regularity scalar functions on open subtypes

For a chosen charted space and a finite natural order, the scalar-function locally
ringed space on an open subtype agrees with the restriction of the ambient locally
ringed space. The comparison factors the morphism induced by the inclusion through
the canonical restriction morphism.

Only the canonically induced charts on an open subtype are considered; the
corresponding statement for arbitrary topological open embeddings requires
compatibility with the chosen charts. The construction parallels the smooth
open-subtype comparison in mathlib's manifold locally ringed spaces and uses the
existing open-immersion restriction API.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), Definition 4.3.9 (p. 142): intrinsic versus restricted scalar functions
  on a local model ball motivate the comparison. Finite natural regularity and
  canonically induced open-subtype charts are project constructions, not an
  arbitrary-chart open-embedding theorem from the source.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite
open scoped ContDiff Manifold

universe u

namespace FiniteRegularityFunctions

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]

/-- The finite-regularity scalar-function morphism induced by inclusion of an
open subtype is an open immersion. -/
instance locallyRingedSpaceMap_subtype_isOpenImmersion (r : ℕ) (U : Opens M) :
    LocallyRingedSpace.IsOpenImmersion
      (locallyRingedSpaceMap IM IM U M r Subtype.val contMDiff_subtype_val) where
  base_open := by
    change IsOpenEmbedding (Subtype.val : U → M)
    exact U.isOpenEmbedding'
  c_iso V := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let inclusion : TopCat.of U ⟶ TopCat.of M :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    have hinclusion : IsOpenEmbedding inclusion.hom := U.isOpenEmbedding'
    let image : Opens M := hinclusion.isOpenMap.functor.obj V
    let preimage : Opens U := (Opens.map inclusion).obj image
    let homeo : preimage ≃ₜ image :=
      U.isOpenEmbedding'.homeomorphOfSubsetRange (Set.image_subset_range _ V.1)
    constructor
    · intro first second heq
      change (sheaf IM M r).presheaf.obj (op image) at first second
      apply section_ext (IM := IM) (M := M) r image
      intro point
      have hvalues := congrArg
        (fun pulled : (sheaf IM U r).presheaf.obj (op preimage) =>
          pulled (homeo.symm point)) heq
      change first (homeo (homeo.symm point)) =
        second (homeo (homeo.symm point)) at hvalues
      simpa only [homeo.apply_symm_apply] using hvalues
    · intro target
      change (sheaf IM U r).presheaf.obj (op preimage) at target
      have hhomeo : ContMDiff IM IM (r : ℕ∞ω) homeo.symm := by
        intro point
        refine (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
          (fun point : image => homeo.symm point) Set.univ point).mp ?_
        refine (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
          (fun point : image => ((homeo.symm point : preimage) : U)) Set.univ point).mp ?_
        have hval : (fun point : image => (homeo.symm point : M)) =
            (Subtype.val : image → M) := by
          funext point
          exact congrArg Subtype.val (homeo.apply_symm_apply point)
        change ContMDiffAt IM IM (r : ℕ∞ω)
          (fun point : image => (homeo.symm point : M)) point
        rw [hval]
        exact contMDiff_subtype_val point
      refine ⟨ofFunction (IM := IM) (M := M) r image
        (fun point => target (homeo.symm point))
        ((section_contMDiff (IM := IM) (M := U) r preimage target).comp hhomeo), ?_⟩
      apply section_ext (IM := IM) (M := U) r preimage
      intro point
      change target (homeo.symm ⟨(point : M), point.2⟩) = target point
      have hpoint : (⟨(point : M), point.2⟩ : image) = homeo point := Subtype.ext rfl
      rw [hpoint, homeo.symm_apply_apply]

/-- Restricting finite-regularity scalar functions to an open subtype gives its
intrinsic finite-regularity scalar-function locally ringed space. -/
def restrictLocallyRingedSpaceIso (r : ℕ) (U : Opens M) :
    (locallyRingedSpace r IM M).restrict U.isOpenEmbedding ≅
      locallyRingedSpace r IM U :=
  (LocallyRingedSpace.IsOpenImmersion.isoRestrict
    (locallyRingedSpaceMap IM IM U M r Subtype.val contMDiff_subtype_val)).symm

/-- The comparison followed by inclusion equals the ambient canonical
restriction morphism. -/
theorem restrictLocallyRingedSpaceIso_hom_ofRestrict (r : ℕ) (U : Opens M) :
    (restrictLocallyRingedSpaceIso IM M r U).hom ≫
        locallyRingedSpaceMap IM IM U M r Subtype.val contMDiff_subtype_val =
      (locallyRingedSpace r IM M).ofRestrict U.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict
    (locallyRingedSpaceMap IM IM U M r Subtype.val contMDiff_subtype_val)

/-- Inclusion is the inverse comparison followed by the ambient canonical
restriction morphism. -/
theorem restrictLocallyRingedSpaceIso_inv_ofRestrict (r : ℕ) (U : Opens M) :
    (restrictLocallyRingedSpaceIso IM M r U).inv ≫
        (locallyRingedSpace r IM M).ofRestrict U.isOpenEmbedding =
      locallyRingedSpaceMap IM IM U M r Subtype.val contMDiff_subtype_val :=
  LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict
    (locallyRingedSpaceMap IM IM U M r Subtype.val contMDiff_subtype_val)

end FiniteRegularityFunctions
