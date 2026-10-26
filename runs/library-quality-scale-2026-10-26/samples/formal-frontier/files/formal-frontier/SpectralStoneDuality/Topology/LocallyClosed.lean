/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.LocallyClosed

/-!
# Compact locally closed subspaces of prespectral spaces

An inducing spectral map into a prespectral quasi-separated space preserves
quasi-separatedness. Compact locally closed subsets of such a space are
retrocompact and have compact, prespectral, quasi-separated subspace topologies.

Unlike the corresponding result for coherent ambient spaces, these conclusions
do not require the ambient space to be compact. Neither they nor the definition
of coherence require separation or sobriety.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.2(a), Proposition 2.2.3. The compact locally closed statements
  here weaken its compact-ambient-space assumption and do not claim sobriety.
- Mathlib, `Topology.Constructible` and `Topology.LocallyClosed`, for the
  locally closed and retrocompact predicates and compact-open basis lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open Set TopologicalSpace

/-- An inducing spectral map into a prespectral quasi-separated space has a
quasi-separated source, even when it is not injective. -/
theorem Topology.IsInducing.quasiSeparatedSpace_of_isSpectralMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace Y] [QuasiSeparatedSpace Y]
    {f : X → Y} (hf : Topology.IsInducing f) (hfs : IsSpectralMap f) :
    QuasiSeparatedSpace X := by
  have hBasis : IsTopologicalBasis
      (Set.range (fun U : {U : Set Y // IsOpen U ∧ IsCompact U} => f ⁻¹' U.1)) := by
    convert hf.isTopologicalBasis PrespectralSpace.isTopologicalBasis using 1
    ext U
    constructor
    · rintro ⟨⟨V, hV⟩, rfl⟩
      exact ⟨V, hV, rfl⟩
    · rintro ⟨V, hV, rfl⟩
      exact ⟨⟨V, hV⟩, rfl⟩
  refine QuasiSeparatedSpace.of_isTopologicalBasis hBasis ?_
  rintro ⟨U, hU⟩ ⟨V, hV⟩
  change IsCompact (f ⁻¹' U ∩ f ⁻¹' V)
  rw [← preimage_inter]
  exact hfs.isCompact_preimage_of_isOpen (hU.1.inter hV.1)
    (hU.2.inter_of_isOpen hV.2 hU.1 hV.1)

/-- Generalizing Fujiwara--Kato, *Foundations of Rigid Geometry I*,
Proposition 2.2.3, a compact locally closed subset of a prespectral quasi-separated space is
retrocompact; the ambient space need not be compact. Compactness allows the open
factor in a locally closed presentation to be replaced by a compact open one. -/
theorem IsCompact.isRetrocompact_of_isLocallyClosed
    {X : Type u} [TopologicalSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
    {Z : Set X} (hZcompact : IsCompact Z) (hZlocal : IsLocallyClosed Z) :
    IsRetrocompact Z := by
  obtain ⟨U, C, hUopen, hCclosed, rfl⟩ := hZlocal
  obtain ⟨W, hWcompact, hWopen, hZW, hWU⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      hZcompact hUopen inter_subset_left
  have hEq : U ∩ C = W ∩ C := by
    apply subset_antisymm
    · exact fun _ hx ↦ ⟨hZW hx, hx.2⟩
    · exact fun _ hx ↦ ⟨hWU hx.1, hx.2⟩
  rw [hEq]
  intro V hVcompact hVopen
  have hWVcompact : IsCompact (W ∩ V) :=
    hWcompact.inter_of_isOpen hVcompact hWopen hVopen
  simpa [inter_assoc, inter_left_comm, inter_comm] using
    hWVcompact.inter_right hCclosed

/-- Generalizing Fujiwara--Kato, *Foundations of Rigid Geometry I*,
Proposition 2.2.3, a compact locally closed subspace of a prespectral quasi-separated space is
itself prespectral, compact and quasi-separated, without requiring a compact
ambient space. These three conditions do not assert sobriety. -/
theorem IsLocallyClosed.subtype_prespectral_compact_quasiSeparated
    {X : Type u} [TopologicalSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
    {Z : Set X} (hZlocal : IsLocallyClosed Z) (hZcompact : IsCompact Z) :
    PrespectralSpace Z ∧ CompactSpace Z ∧ QuasiSeparatedSpace Z := by
  have hZspectral : IsSpectralMap (Subtype.val : Z → X) :=
    IsRetrocompact_iff_isSpectralMap_subtypeVal.mp
      (hZcompact.isRetrocompact_of_isLocallyClosed hZlocal)
  exact ⟨PrespectralSpace.of_isInducing Subtype.val .subtypeVal hZspectral,
    isCompact_iff_compactSpace.mp hZcompact,
    Topology.IsInducing.quasiSeparatedSpace_of_isSpectralMap .subtypeVal hZspectral⟩
