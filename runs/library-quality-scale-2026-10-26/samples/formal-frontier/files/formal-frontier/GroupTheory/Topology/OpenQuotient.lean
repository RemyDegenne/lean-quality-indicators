/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Separation.Profinite
public import GroupTheory.Topology.CompactOpenSubgroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Open quotients of compact totally disconnected spaces

An open quotient of a compact Hausdorff totally disconnected space is totally
disconnected when its codomain is Hausdorff. This general topology result was
first formalized in Formal Frontier's Profinite Groups library.

An open surjective continuous homomorphism from a locally compact totally
disconnected group to a Hausdorff group also has totally disconnected target:
the compact result applies to its restriction to a compact open subgroup.

The proof uses Mathlib's clopen basis of a compact Hausdorff totally
disconnected space and its transport along an open quotient map.

## References

- Formal Frontier, *Profinite Groups*, continuous sections of profinite coset
  projections (original formalization of the open-quotient theorem).
- Mathlib, `Mathlib.Topology.Separation.Profinite` and
  `Mathlib.Topology.Bases` (clopen basis and open-quotient basis transport).
-/

@[expose] public section

open Function Set TopologicalSpace
open scoped Topology

universe u v

namespace Topology.IsOpenQuotientMap

/-- An open Hausdorff quotient of a compact Hausdorff totally disconnected
space is totally disconnected. -/
theorem totallyDisconnectedSpace
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : IsOpenQuotientMap f) : TotallyDisconnectedSpace Y := by
  have hb := hf.isTopologicalBasis (isTopologicalBasis_isClopen (X := X))
  have hbc : Set.image f '' {U : Set X | IsClopen U} ⊆ {V : Set Y | IsClopen V} := by
    rintro _ ⟨U, hU, rfl⟩
    exact ⟨(hU.1.isCompact.image hf.continuous).isClosed, hf.isOpenMap U hU.2⟩
  let _ : TotallySeparatedSpace Y := totallySeparatedSpace_of_t0_of_basis_clopen <|
    hb.of_isOpen_of_subset (fun _ h ↦ h.2) hbc
  infer_instance

end Topology.IsOpenQuotientMap

namespace ContinuousMonoidHom

/-- An open quotient of a locally compact totally disconnected topological group
is totally disconnected if its target is Hausdorff. The domain need not be compact. -/
theorem totallyDisconnectedSpace_of_isOpenQuotientMap
    {G : Type u} {H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [SeparatelyContinuousMul H] [T2Space H]
    (hom : G →ₜ* H) (hopen : IsOpenQuotientMap (hom : G → H)) :
    TotallyDisconnectedSpace H := by
  let _ : T2Space G :=
    IsTopologicalGroup.t2Space_iff_one_closed.mpr isClosed_singleton
  obtain ⟨K, hKcompact, -⟩ := OpenSubgroup.exists_compact_subset_nhds_one
    (W := Set.univ) (Filter.univ_mem : (Set.univ : Set G) ∈ 𝓝 (1 : G))
  let P : OpenSubgroup H := ⟨(K : Subgroup G).map hom.toMonoidHom, by
    exact hopen.isOpenMap _ K.isOpen⟩
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let restricted : K → P := fun element =>
    ⟨hom element, ⟨element.1, element.2, rfl⟩⟩
  have hrestricted : IsOpenQuotientMap restricted := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨target, ⟨element, helement, heq⟩⟩
      exact ⟨⟨element, helement⟩, Subtype.ext heq⟩
    · exact (hom.continuous_toFun.comp continuous_subtype_val).subtype_mk _
    · exact (hopen.isOpenMap.domRestrict K.isOpen).subtype_mk _
  let _ : TotallyDisconnectedSpace P :=
    Topology.IsOpenQuotientMap.totallyDisconnectedSpace hrestricted
  apply totallyDisconnectedSpace_iff_connectedComponent_one.mpr
  have hsubset : connectedComponent (1 : H) ⊆ (P : Set H) :=
    P.isClopen.connectedComponent_subset P.one_mem
  exact (totallyDisconnectedSpace_subtype_iff.mp inferInstance _ hsubset
    isPreconnected_connectedComponent).eq_singleton_of_mem mem_connectedComponent

end ContinuousMonoidHom
