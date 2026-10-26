/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.KrullDimension

/-!
# Topological Krull dimension and open covers

The topological Krull dimension of a space is the supremum of the dimensions of a jointly
surjective family of open embeddings into it. The ambient space, index type and chart
domains have independent universes. In particular, the dimension is the supremum of the
dimensions of the open subspaces in any open cover, with their induced topologies.

The supremum is taken in `WithBot ℕ∞`. An empty-index cover of the empty space has
dimension `⊥`, not zero. Arbitrary infinite covers and unbounded dimensions are included:
the supremum need not be attained by a member of the cover.

## References

* Mathlib's `Mathlib.Topology.KrullDimension` for topological Krull dimension and
  open-embedding coheight invariance.
* Mathlib's `Mathlib.Order.KrullDimension` for the empty-safe supremum-of-coheights formula.
-/

@[expose] public section

universe u v w

/-- A space's topological Krull dimension is the supremum of the dimensions of the domains
of any jointly surjective family of open embeddings into it.

The given chart domains and their topologies are retained. No separation, sobriety,
Noetherianity, quasi-compactness, finiteness, nonemptiness or dimension bound is assumed.
The supremum is in `WithBot ℕ∞`, including the empty and infinite cases. -/
theorem topologicalKrullDim_eq_iSup_of_isOpenEmbedding_cover
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    {Y : ι → Type w} [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, Y i → X) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hcov : ∀ x : X, ∃ i, ∃ y : Y i, f i y = x) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  refine le_antisymm ?_ (iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le)
  calc
    topologicalKrullDim X =
        ⨆ Z : TopologicalSpace.IrreducibleCloseds X, (Order.coheight Z : WithBot ℕ∞) :=
      Order.krullDim_eq_iSup_coheight
    _ ≤ ⨆ i, topologicalKrullDim (Y i) := by
      refine iSup_le fun Z => ?_
      obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
      obtain ⟨i, y, hfy⟩ := hcov x
      have hpre : ((f i) ⁻¹' (Z : Set X)).Nonempty := by
        refine ⟨y, ?_⟩
        simpa only [Set.mem_preimage, hfy] using hx
      let W : TopologicalSpace.IrreducibleCloseds (Y i) :=
        ⟨(f i) ⁻¹' (Z : Set X),
          Z.isIrreducible.preimage (hf i) ⟨x, hx, y, hfy⟩,
          IsClosed.preimage (hf i).continuous Z.isClosed⟩
      have hW : (W : Set (Y i)) = (f i) ⁻¹' (Z : Set X) :=
        TopologicalSpace.IrreducibleCloseds.coe_mk _ _ _
      have hmap : TopologicalSpace.IrreducibleCloseds.map (f i) (hf i).continuous W = Z := by
        apply TopologicalSpace.IrreducibleCloseds.ext
        rw [TopologicalSpace.IrreducibleCloseds.coe_map, hW]
        exact closure_image_preimage_of_isPreirreducible (f i) (hf i).isOpenMap
          (Z : Set X) hpre Z.isIrreducible.isPreirreducible Z.isClosed
      calc
        (Order.coheight Z : WithBot ℕ∞) = (Order.coheight W : WithBot ℕ∞) := by
          rw [← hmap, (hf i).coheight_map]
        _ ≤ topologicalKrullDim (Y i) := Order.coheight_le_krullDim W
        _ ≤ ⨆ j, topologicalKrullDim (Y j) :=
          le_iSup (fun j : ι => topologicalKrullDim (Y j)) i

/-- The topological Krull dimension of a space equals the supremum of the dimensions of
its open subspaces in an arbitrary open cover.

Each open subspace carries the topology induced from the original space. The supremum
is in `WithBot ℕ∞`, including the empty and infinite cases. -/
theorem topologicalKrullDim_eq_iSup_of_isOpen_cover
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (U i) := by
  refine topologicalKrullDim_eq_iSup_of_isOpenEmbedding_cover
    (fun i => (Subtype.val : U i → X)) (fun i => (hU i).isOpenEmbedding_subtypeVal) ?_
  intro x
  have hx : x ∈ ⋃ i, U i := by
    rw [hcov]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨i, ⟨x, hi⟩, rfl⟩
