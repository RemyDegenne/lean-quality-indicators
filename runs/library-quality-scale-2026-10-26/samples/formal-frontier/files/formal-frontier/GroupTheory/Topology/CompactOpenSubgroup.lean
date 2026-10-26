/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Compact open subgroups of totally disconnected locally compact groups

The left-translation stabilizer of any compact open set is an open subgroup. When the set
contains the identity, the stabilizer is compact and contained in it. Such subgroups form
an identity-neighborhood basis in a totally disconnected locally compact topological group.
No ambient compactness or separation assumption is needed for the stabilizer construction.

## References

* Van Dantzig's compact-open subgroup theorem, used by Neukirch, Schmidt, and Wingberg,
  *Cohomology of Number Fields*, Chapter I, §1, in the identity-component discussion.
* Mathlib's `OpenSubgroup`, `MulAction.stabilizer`, `compact_open_separated_mul_left`,
  `exists_compact_subset`, and `loc_compact_Haus_tot_disc_of_zero_dim` provide the
  underlying algebraic and topological interfaces.

The stabilizer argument independently assembles these ingredients; it does not transcribe
either of the other works cited for the theorem in the source.
-/

@[expose] public section

open Filter
open scoped Pointwise Topology

universe u

namespace OpenSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The open subgroup fixing a compact open set by left translation.
Its carrier agrees with Mathlib's action stabilizer of the underlying set. -/
def leftStabilizer [IsTopologicalGroup G] (K : Set G) (hK : IsCompact K)
    (hK_open : IsOpen K) : OpenSubgroup G where
  toSubgroup := MulAction.stabilizer G K
  isOpen' := by
    obtain ⟨V, hV, hVK⟩ := compact_open_separated_mul_left hK hK_open (Set.Subset.rfl)
    have hmul (g : G) (hg : g ∈ V) : g • K ⊆ K :=
      (Set.smul_set_subset_mul hg).trans hVK
    apply Subgroup.isOpen_of_mem_nhds (MulAction.stabilizer G K)
    refine Filter.mem_of_superset (Filter.inter_mem hV (inv_mem_nhds_one G hV)) ?_
    intro g hg
    change g ∈ MulAction.stabilizer G K
    rw [MulAction.mem_stabilizer_iff]
    apply Set.Subset.antisymm (hmul g hg.1)
    exact Set.subset_smul_set_iff.mpr (hmul g⁻¹ (Set.mem_inv.mp hg.2))

/-- Membership in the left-translation stabilizer means preserving the set exactly. -/
@[simp]
theorem mem_leftStabilizer_iff [IsTopologicalGroup G] {K : Set G}
    (hK : IsCompact K) (hK_open : IsOpen K) {g : G} :
    g ∈ leftStabilizer K hK hK_open ↔ g • K = K :=
  MulAction.mem_stabilizer_iff

/-- The translation stabilizer of an identity-containing set lies in that set. -/
theorem leftStabilizer_subset [IsTopologicalGroup G] {K : Set G}
    (hK : IsCompact K) (hK_open : IsOpen K)
    (hone : (1 : G) ∈ K) :
    (leftStabilizer K hK hK_open : Set G) ⊆ K := by
  intro g hg
  have hfix : g • K = K := (mem_leftStabilizer_iff hK hK_open).mp hg
  have hmem : g • (1 : G) ∈ g • K := Set.smul_mem_smul_set_iff.mpr hone
  simpa only [hfix, smul_eq_mul, mul_one] using hmem

/-- The translation stabilizer is compact, without assuming the ambient group Hausdorff. -/
theorem isCompact_leftStabilizer [IsTopologicalGroup G] {K : Set G}
    (hK : IsCompact K) (hK_open : IsOpen K)
    (hone : (1 : G) ∈ K) :
    IsCompact (leftStabilizer K hK hK_open : Set G) :=
  hK.of_isClosed_subset (leftStabilizer K hK hK_open).isClosed
    (leftStabilizer_subset hK hK_open hone)

/-- A compact open set containing the identity contains a compact open subgroup. -/
theorem exists_compact_subset_of_compact_open [IsTopologicalGroup G]
    {K : Set G} (hK : IsCompact K)
    (hK_open : IsOpen K) (hone : (1 : G) ∈ K) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ K :=
  ⟨leftStabilizer K hK hK_open, isCompact_leftStabilizer hK hK_open hone,
    leftStabilizer_subset hK hK_open hone⟩

/-- In a compact ambient group, the compactness refinement agrees with the existential
conclusion of Mathlib's `IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one`.
This equivalence does not require the containing set itself to be clopen. -/
theorem exists_compact_subset_iff_exists_subset [CompactSpace G]
    [SeparatelyContinuousMul G] {W : Set G} :
    (∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ W) ↔
      ∃ H : OpenSubgroup G, (H : Set G) ⊆ W := by
  constructor
  · rintro ⟨H, -, hHW⟩
    exact ⟨H, hHW⟩
  · rintro ⟨H, hHW⟩
    exact ⟨H, H.isClosed.isCompact, hHW⟩

/-- Van Dantzig's compact-open subgroup theorem, used in Neukirch, Schmidt, and Wingberg,
*Cohomology of Number Fields*, Chapter I, §1: every identity neighborhood contains a compact
open subgroup, even when the neighborhood is not open. Total disconnectedness supplies
Hausdorffness for topological groups; it is not an extra hypothesis. -/
theorem exists_compact_subset_nhds_one [IsTopologicalGroup G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] {W : Set G} (hW : W ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ W := by
  have hT2 : T2Space G :=
    IsTopologicalGroup.t2Space_iff_one_closed.mpr isClosed_singleton
  obtain ⟨U, hUW, hUopen, hUone⟩ := mem_nhds_iff.mp hW
  obtain ⟨S, hScompact, hSone, hSU⟩ := exists_compact_subset hUopen hUone
  have hBasis : TopologicalSpace.IsTopologicalBasis {K : Set G | IsClopen K} :=
    @loc_compact_Haus_tot_disc_of_zero_dim G _ _ hT2 _
  obtain ⟨K, hKclopen, hKone, hKS⟩ :=
    hBasis.mem_nhds_iff.mp (isOpen_interior.mem_nhds hSone)
  have hKcompact : IsCompact K :=
    hScompact.of_isClosed_subset hKclopen.1 (hKS.trans interior_subset)
  obtain ⟨H, hHcompact, hHK⟩ :=
    exists_compact_subset_of_compact_open hKcompact hKclopen.2 hKone
  exact ⟨H, hHcompact, hHK.trans (hKS.trans (interior_subset.trans (hSU.trans hUW)))⟩

/-- The neighborhood-basis form of van Dantzig's theorem, used in Neukirch, Schmidt, and
Wingberg, *Cohomology of Number Fields*, Chapter I, §1: compact open subgroups form a basis
of identity neighborhoods. -/
theorem nhds_one_hasBasis_compact [IsTopologicalGroup G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G => IsCompact (H : Set G))
      (fun H => (H : Set G)) := by
  constructor
  intro W
  constructor
  · exact exists_compact_subset_nhds_one
  · rintro ⟨H, -, hHW⟩
    exact mem_of_superset H.mem_nhds_one hHW

end OpenSubgroup

end
