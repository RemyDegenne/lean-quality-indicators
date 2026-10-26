/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.Bases
public import Mathlib.Topology.Spectral.Basic

public section

set_option warningAsError true

/-!
# Compact opens of subspaces

This file lifts compact open subsets of an arbitrary subspace to compact open
subsets of an ambient space with a compact-open basis. As an application, it
detects spectrality of a map to a subspace after composing with the inclusion.

## References

- Mathlib, `Topology.Compactness.Bases` and `Topology.Spectral.Basic`, for
  compact-open bases and spectral-map predicates used in the lifting proof.
-/

open Function Set TopologicalSpace

universe u v

namespace SpectralStoneDuality

variable {X : Type u} [TopologicalSpace X]

/-- A compact open subset of an arbitrary subspace is the intersection with a
compact open subset of the ambient space, provided a compact-open basis is
available. -/
theorem exists_compactOpen_image_eq_inter_of_basis {Y : Set X} {V : Set Y}
    {b : Set (Set X)} (hb : IsTopologicalBasis b)
    (hbc : ∀ U ∈ b, IsCompact U) (hVo : IsOpen V) (hVc : IsCompact V) :
    ∃ U : CompactOpens X, Subtype.val '' V = Y ∩ (U : Set X) := by
  obtain ⟨W, hWo, hVW⟩ := hVo.image_val
  let S : Set X := Subtype.val '' V
  have hSc : IsCompact S := hVc.image continuous_subtype_val
  have hSW : S ⊆ W := by
    rw [show S = W ∩ Y by simpa [S] using hVW]
    exact inter_subset_left
  have hSY : S ⊆ Y := by
    rw [show S = W ∩ Y by simpa [S] using hVW]
    exact inter_subset_right
  choose B hBb hxB hBW using fun x : S ↦ hb.exists_subset_of_mem_open (hSW x.2) hWo
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover B (fun x ↦ hb.isOpen (hBb x)) (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxB ⟨x, hx⟩⟩)
  let U : CompactOpens X :=
    ⟨⟨⋃ x ∈ t, B x, t.finite_toSet.isCompact_biUnion fun x _ ↦ hbc _ (hBb x)⟩,
      isOpen_biUnion fun x _ ↦ hb.isOpen (hBb x)⟩
  refine ⟨U, ?_⟩
  change S = Y ∩ ⋃ x ∈ t, B x
  apply Subset.antisymm
  · intro x hx
    exact ⟨hSY hx, ht hx⟩
  · rintro x ⟨hxY, hxU⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
    show x ∈ S
    rw [show S = W ∩ Y by simpa [S] using hVW]
    exact ⟨hBW i hxi, hxY⟩

/-- A compact open subset of an arbitrary subspace of a prespectral space is
the intersection with a compact open subset of the ambient space. -/
theorem exists_compactOpen_image_eq_inter [PrespectralSpace X]
    {Y : Set X} {V : Set Y} (hVo : IsOpen V) (hVc : IsCompact V) :
    ∃ U : CompactOpens X, Subtype.val '' V = Y ∩ (U : Set X) :=
  exists_compactOpen_image_eq_inter_of_basis
    PrespectralSpace.isTopologicalBasis
    (fun _ hU ↦ hU.2) hVo hVc

/-- A map to a subspace of a prespectral space is spectral when its composite
with the inclusion is spectral. -/
theorem isSpectralMap_to_subtype_of_comp [PrespectralSpace X]
    {Y : Set X} {Z : Type v} [TopologicalSpace Z] (g : Z → Y)
    (hg : IsSpectralMap ((Subtype.val : Y → X) ∘ g)) : IsSpectralMap g := by
  refine ⟨?_, ?_⟩
  · convert hg.continuous.subtype_mk (fun z ↦ (g z).2) using 1
    ext z
    rfl
  · intro V hVo hVc
    obtain ⟨U, hVU⟩ := exists_compactOpen_image_eq_inter hVo hVc
    have hVUpre : V = (Subtype.val : Y → X) ⁻¹' (U : Set X) := by
      ext y
      constructor
      · intro hy
        have hy' : (y : X) ∈ Subtype.val '' V := ⟨y, hy, rfl⟩
        exact (show (y : X) ∈ Y ∩ (U : Set X) by simpa [hVU] using hy').2
      · intro hy
        have hy' : (y : X) ∈ Subtype.val '' V := by
          rw [hVU]
          exact ⟨y.2, hy⟩
        obtain ⟨y', hy'V, hy'y⟩ := hy'
        have : y' = y := Subtype.ext hy'y
        simpa only [this] using hy'V
    rw [hVUpre, preimage_preimage]
    exact hg.isCompact_preimage_of_isOpen U.isOpen U.isCompact

end SpectralStoneDuality
