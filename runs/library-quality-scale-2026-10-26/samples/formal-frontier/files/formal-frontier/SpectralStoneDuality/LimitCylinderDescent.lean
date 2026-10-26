/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Limits
public import SpectralStoneDuality.Subspace
public import SpectralStoneDuality.Topology.LocallyClosed
public import Mathlib.CategoryTheory.Filtered.Final

public section

set_option warningAsError true

/-!
# Eventual containment of compact-open limit cylinders

For a cofiltered diagram of spectral spaces with spectral transition maps,
inclusion of a compact-open cylinder in an open cylinder over an actual
limiting cone already holds over some stage. No nonemptiness or surjectivity
condition is imposed on either the stages or the limit.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.2(a), Proposition 2.2.3, for compact locally closed subspaces.
  The cylinder-containment equivalence is a separate generalization for
  arbitrary supplied limiting cones, not a numbered theorem there.
- Mathlib, `CategoryTheory.Filtered.Final` and
  `Topology.Category.TopCat.Limits.Cofiltered`, for initiality of the
  over-category and limit-cone machinery.
-/

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology
open scoped Set.Notation

universe u v

noncomputable section

namespace SpectralStoneDuality

private theorem compactLocallyClosed_spectral {X : Type u}
    [TopologicalSpace X] [SpectralSpace X] {Z : Set X}
    (hZcompact : IsCompact Z) (hZlocal : IsLocallyClosed Z) :
    SpectralSpace Z := by
  obtain ⟨hZpre, hZcompactSpace, hZqs⟩ :=
    hZlocal.subtype_prespectral_compact_quasiSeparated hZcompact
  let _ : PrespectralSpace Z := hZpre
  let _ : CompactSpace Z := hZcompactSpace
  let _ : QuasiSeparatedSpace Z := hZqs
  obtain ⟨U, C, hUopen, hCclosed, hZeq⟩ := hZlocal
  let _ : QuasiSober U := hUopen.isOpenEmbedding_subtypeVal.quasiSober
  have hSober : QuasiSober Z := by
    rw [hZeq]
    exact QuasiSober.inter_of_isClosed_of_quasiSober_left (W := U) hCclosed
  exact {
    toT0Space := inferInstance
    toCompactSpace := inferInstance
    toQuasiSober := hSober
    toQuasiSeparatedSpace := inferInstance
    toPrespectralSpace := inferInstance }

variable {J : Type v} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u}) (i : J)

private def counterexampleSet (U V : Set (F.obj i)) (X : Over i) :
    Set (F.obj X.left) :=
  F.map X.hom ⁻¹' U \ F.map X.hom ⁻¹' V

omit [IsCofiltered J] in
private theorem counterexampleSet_preimage (U V : Set (F.obj i))
    {X Y : Over i} (f : X ⟶ Y) :
    F.map f.left ⁻¹' counterexampleSet F i U V Y =
      counterexampleSet F i U V X := by
  ext x
  simp only [counterexampleSet, mem_preimage, mem_sdiff]
  have hcomp : F.map Y.hom (F.map f.left x) = F.map X.hom x := by
    change (F.map f.left ≫ F.map Y.hom) x = F.map X.hom x
    rw [← F.map_comp, f.w]
  rw [hcomp]

omit [IsCofiltered J] in
private theorem counterexampleSet_compact_locallyClosed
    (hmap : ∀ {a b : J} (f : a ⟶ b), IsSpectralMap (F.map f))
    (U V : Set (F.obj i)) (hUopen : IsOpen U) (hUcompact : IsCompact U)
    (hVopen : IsOpen V) (X : Over i) :
    IsCompact (counterexampleSet F i U V X) ∧
      IsLocallyClosed (counterexampleSet F i U V X) := by
  have hAopen : IsOpen (F.map X.hom ⁻¹' U) :=
    hUopen.preimage (hmap X.hom).continuous
  have hAcompact : IsCompact (F.map X.hom ⁻¹' U) :=
    hUcompact.preimage_of_isOpen (hmap X.hom) hUopen
  have hBclosed : IsClosed (F.map X.hom ⁻¹' V)ᶜ :=
    (hVopen.preimage (hmap X.hom).continuous).isClosed_compl
  constructor
  · simpa only [counterexampleSet, Set.sdiff_eq] using
      hAcompact.inter_right hBclosed
  · exact ⟨_, _, hAopen, hBclosed, by simp only [counterexampleSet, Set.sdiff_eq]⟩

omit [IsCofiltered J] in
private theorem counterexampleSet_spectral
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {a b : J} (f : a ⟶ b), IsSpectralMap (F.map f))
    (U V : Set (F.obj i)) (hUopen : IsOpen U) (hUcompact : IsCompact U)
    (hVopen : IsOpen V) (X : Over i) :
    SpectralSpace (counterexampleSet F i U V X) := by
  let _ : SpectralSpace (F.obj X.left) := hX X.left
  exact compactLocallyClosed_spectral
    (counterexampleSet_compact_locallyClosed F i hmap U V
      hUopen hUcompact hVopen X).1
    (counterexampleSet_compact_locallyClosed F i hmap U V
      hUopen hUcompact hVopen X).2

private def counterexampleMap (U V : Set (F.obj i))
    {X Y : Over i} (f : X ⟶ Y) :
    TopCat.of (counterexampleSet F i U V X) ⟶
      TopCat.of (counterexampleSet F i U V Y) :=
  TopCat.ofHom {
    toFun := fun x ↦ ⟨F.map f.left x, by
      change x.1 ∈ F.map f.left ⁻¹' counterexampleSet F i U V Y
      rw [counterexampleSet_preimage F i U V f]
      exact x.2⟩
    continuous_toFun := by
      apply Continuous.subtype_map (F.map f.left).hom.continuous
      intro x hx
      change x ∈ F.map f.left ⁻¹' counterexampleSet F i U V Y
      rwa [counterexampleSet_preimage F i U V f] }

omit [IsCofiltered J] in
private theorem counterexampleMap_spectral
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {a b : J} (f : a ⟶ b), IsSpectralMap (F.map f))
    (U V : Set (F.obj i)) (hUopen : IsOpen U) (hUcompact : IsCompact U)
    (hVopen : IsOpen V) {X Y : Over i} (f : X ⟶ Y) :
    IsSpectralMap (counterexampleMap F i U V f) := by
  let _ : SpectralSpace (F.obj X.left) := hX X.left
  have hZX := counterexampleSet_compact_locallyClosed F i hmap U V
    hUopen hUcompact hVopen X
  have hIncl : IsSpectralMap
      ((Subtype.val : counterexampleSet F i U V X → F.obj X.left)) :=
    IsRetrocompact_iff_isSpectralMap_subtypeVal.mp
      (hZX.1.isRetrocompact_of_isLocallyClosed hZX.2)
  apply SpectralStoneDuality.isSpectralMap_to_subtype_of_comp
  change IsSpectralMap ((F.map f.left) ∘
    (Subtype.val : counterexampleSet F i U V X → F.obj X.left))
  exact (hmap f.left).comp hIncl

private def counterexampleDiagram (U V : Set (F.obj i)) :
    Over i ⥤ TopCat.{max v u} where
  obj X := TopCat.of (counterexampleSet F i U V X)
  map f := counterexampleMap F i U V f
  map_id X := by
    apply TopCat.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    change F.map (𝟙 X.left) x = x
    rw [F.map_id]
    rfl
  map_comp f g := by
    apply TopCat.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    change F.map (f.left ≫ g.left) x = F.map g.left (F.map f.left x)
    rw [F.map_comp]
    rfl

private def counterexampleCone (U V : Set (F.obj i)) :
    Cone (Over.forget i ⋙ F) where
  pt := (TopCat.limitCone (counterexampleDiagram F i U V)).pt
  π := (TopCat.limitCone (counterexampleDiagram F i U V)).π ≫
    { app X := TopCat.ofHom {
        toFun := Subtype.val
        continuous_toFun := continuous_subtype_val }
      naturality X Y f := by
        apply TopCat.ext
        rintro ⟨x, hx⟩
        rfl }

private theorem counterexampleLimit_nonempty
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {a b : J} (f : a ⟶ b), IsSpectralMap (F.map f))
    (U V : Set (F.obj i)) (hUopen : IsOpen U) (hUcompact : IsCompact U)
    (hVopen : IsOpen V)
    (hne : ∀ X : Over i, ¬ (F.map X.hom ⁻¹' U ⊆ F.map X.hom ⁻¹' V)) :
    Nonempty (TopCat.limitCone (counterexampleDiagram F i U V)).pt := by
  apply SpectralStoneDuality.nonempty_limit_of_spectral
    (counterexampleDiagram F i U V)
  · exact fun X ↦ counterexampleSet_spectral F i hX hmap U V
      hUopen hUcompact hVopen X
  · exact fun f ↦ counterexampleMap_spectral F i hX hmap U V
      hUopen hUcompact hVopen f
  · intro X
    obtain ⟨x, hxU, hxV⟩ := Set.not_subset.mp (hne X)
    exact ⟨⟨x, ⟨hxU, hxV⟩⟩⟩

/-- Inclusion of compact-open and open cylinders over an arbitrary actual
limiting cone is witnessed at a stage over their common index. -/
theorem limitCylinder_subset_iff_eventually
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {a b : J} (f : a ⟶ b), IsSpectralMap (F.map f))
    (C : Cone F) (hC : IsLimit C)
    (U V : Set (F.obj i)) (hUopen : IsOpen U) (hUcompact : IsCompact U)
    (hVopen : IsOpen V) :
    C.π.app i ⁻¹' U ⊆ C.π.app i ⁻¹' V ↔
      ∃ X : Over i, F.map X.hom ⁻¹' U ⊆ F.map X.hom ⁻¹' V := by
  constructor
  · intro hlimit
    by_contra hstage
    have hne : ∀ X : Over i,
        ¬ (F.map X.hom ⁻¹' U ⊆ F.map X.hom ⁻¹' V) := by
      intro X hsub
      exact hstage ⟨X, hsub⟩
    obtain ⟨z⟩ := counterexampleLimit_nonempty F i hX hmap U V
      hUopen hUcompact hVopen hne
    let T := counterexampleCone F i U V
    let hTail : IsLimit (C.whisker (Over.forget i)) :=
      (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) C).symm hC
    let y : C.pt := hTail.lift T z
    let I : Over i := Over.mk (𝟙 i)
    have hzi : F.map I.hom
        (((TopCat.limitCone (counterexampleDiagram F i U V)).π.app I z).1) ∈
        U \ V :=
      (((TopCat.limitCone (counterexampleDiagram F i U V)).π.app I z).2)
    have hfac := congrArg (fun q ↦ q z) (hTail.fac T I)
    have hy : C.π.app i y ∈ U \ V := by
      change C.π.app i y =
        (((TopCat.limitCone (counterexampleDiagram F i U V)).π.app I z).1)
          at hfac
      have hid : F.map I.hom
          (((TopCat.limitCone (counterexampleDiagram F i U V)).π.app I z).1) =
          (((TopCat.limitCone (counterexampleDiagram F i U V)).π.app I z).1) := by
        change F.map (𝟙 i) _ = _
        rw [F.map_id]
        rfl
      rwa [hid, ← hfac] at hzi
    exact hy.2 (hlimit hy.1)
  · rintro ⟨X, hstage⟩ x hxU
    have hfac := congrArg (fun q ↦ q x) (C.w X.hom)
    have hproj : F.map X.hom (C.π.app X.left x) = C.π.app i x := by
      simpa only [TopCat.coe_comp, Function.comp_apply] using hfac
    have hxStage : (C.π.app X.left x) ∈ F.map X.hom ⁻¹' U := by
      change F.map X.hom (C.π.app X.left x) ∈ U
      rw [hproj]
      exact hxU
    have := hstage hxStage
    change C.π.app i x ∈ V
    rwa [← hproj]

/-- The same descent criterion for the chosen limit. -/
theorem chosenLimitCylinder_subset_iff_eventually
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {a b : J} (f : a ⟶ b), IsSpectralMap (F.map f))
    [HasLimit F]
    (U V : Set (F.obj i)) (hUopen : IsOpen U) (hUcompact : IsCompact U)
    (hVopen : IsOpen V) :
    (limit.π F i) ⁻¹' U ⊆ (limit.π F i) ⁻¹' V ↔
      ∃ X : Over i, F.map X.hom ⁻¹' U ⊆ F.map X.hom ⁻¹' V := by
  exact limitCylinder_subset_iff_eventually F i hX hmap
    (limit.cone F) (limit.isLimit F) U V hUopen hUcompact hVopen

/-- A neighborhood of the range of a limiting projection contains a compact-open
neighborhood whose inverse image is eventually the entire stage. -/
theorem exists_compactOpen_eventually_full
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {a b : J} (f : a ⟶ b), IsSpectralMap (F.map f))
    (C : Cone F) (hC : IsLimit C)
    (U : Set (F.obj i)) (hUopen : IsOpen U)
    (hRange : Set.range (C.π.app i) ⊆ U) :
    ∃ W : Set (F.obj i), IsOpen W ∧ IsCompact W ∧
      Set.range (C.π.app i) ⊆ W ∧ W ⊆ U ∧
      ∃ X : Over i, F.map X.hom ⁻¹' W = Set.univ := by
  let _ (j : J) : SpectralSpace (F.obj j) := hX j
  have hCompact : CompactSpace C.pt := by
    let _ : CompactSpace (TopCat.limitCone F).pt :=
      SpectralStoneDuality.compactSpace_limit_of_spectral F hX hmap
    let e := (TopCat.limitConeIsLimit F).conePointUniqueUpToIso hC
    exact (TopCat.homeoOfIso e).surjective.compactSpace
      (TopCat.homeoOfIso e).continuous
  let _ : CompactSpace C.pt := hCompact
  have hRangeCompact : IsCompact (Set.range (C.π.app i)) :=
    isCompact_range (f := fun x : C.pt ↦ C.π.app i x)
      (show Continuous (fun x : C.pt ↦ C.π.app i x) from
        (C.π.app i).hom.continuous)
  obtain ⟨W, hWcompact, hWopen, hRangeW, hWU⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hRangeCompact hUopen hRange
  refine ⟨W, hWopen, hWcompact, hRangeW, hWU, ?_⟩
  obtain ⟨X, hstage⟩ := (limitCylinder_subset_iff_eventually F i hX hmap
    C hC Set.univ W isOpen_univ isCompact_univ hWopen).mp (by
      intro x _
      exact hRangeW ⟨x, rfl⟩)
  refine ⟨X, Set.eq_univ_of_univ_subset ?_⟩
  simpa only [Set.preimage_univ] using hstage

end SpectralStoneDuality
