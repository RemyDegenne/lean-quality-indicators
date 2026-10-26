/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.RingTheory.KrullDimension.FiniteCapture
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Krull dimension of directed subsemiring unions

For a nonempty directed family of subsemirings of a commutative semiring, the
Krull dimension of its supremum is at most the supremum of the stage dimensions.
The bound takes values in `WithBot ℕ∞`, so it includes empty spectra and infinite
dimension. The index type has no order structure; directedness refers only to
inclusion between members of the family.

Mathlib's `Subsemiring.mem_iSup_of_directed` identifies this supremum with the
set-theoretic union. Its directed finite-union capture lemma places every finite
subset in one stage. Applying `ringKrullDim_le_iSup_of_finite_subset_range` to the
canonical stage inclusions gives the dimension bound.

## Limitations

Nonemptiness supplies a stage even for the empty finite subset. An empty family
is vacuously directed, but its supremum is the bottom subsemiring, which contains
zero and one; its dimension need not be `⊥`, whereas the supremum of the empty
family of dimensions is `⊥`. Directedness is also essential: over a field, the
coordinate polynomial subrings `k[X]` and `k[Y]` of `k[X,Y]` each have dimension
one, while their generated subring has dimension two. Without directedness, the
lattice supremum can introduce mixed sums and products not lying in either stage.

## References

The union and inclusion constructions are Mathlib's `Subsemiring` API. The
finite-common-stage argument uses
`Directed.exists_mem_subset_of_finset_subset_biUnion`, and the dimension argument
uses the finite-subset capture criterion in this library. No directed-colimit
presentation or injectivity assumption on an auxiliary system is required.
-/

@[expose] public section

universe u v

namespace Subsemiring

/-- The Krull dimension of the union of a nonempty directed family of subsemirings
is at most the supremum of their Krull dimensions. The index and ambient-semiring
universes are independent. No order on the index, Noetherianity, nontriviality or
finite-dimensionality hypothesis is required. -/
theorem ringKrullDim_iSup_le
    {ι : Type u} {R : Type v} [CommSemiring R] [Nonempty ι]
    (s : ι → Subsemiring R) (hs : Directed (· ≤ ·) s) :
    ringKrullDim (⨆ i, s i : Subsemiring R) ≤ ⨆ i, ringKrullDim (s i) := by
  classical
  apply ringKrullDim_le_iSup_of_finite_subset_range
    (fun i => Subsemiring.inclusion (le_iSup s i))
  intro E hE
  have hdir : Directed (· ⊆ ·) (fun i => (s i : Set R)) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hs i j
    exact ⟨k, SetLike.coe_subset_coe.mpr hik, SetLike.coe_subset_coe.mpr hjk⟩
  have hfinite : (Subtype.val '' E : Set R).Finite := hE.image Subtype.val
  have hcover : Subtype.val '' E ⊆ ⋃ i, (s i : Set R) := by
    rintro _ ⟨x, _, rfl⟩
    exact Set.mem_iUnion.mpr ((Subsemiring.mem_iSup_of_directed hs).mp x.property)
  have hstage : ∃ i, Subtype.val '' E ⊆ (s i : Set R) := by
    simpa only [hfinite.coe_toFinset] using
      hdir.exists_mem_subset_of_finset_subset_biUnion
        (s := hfinite.toFinset) (by simpa only [hfinite.coe_toFinset] using hcover)
  obtain ⟨i, hi⟩ := hstage
  refine ⟨i, fun x hx => ?_⟩
  exact ⟨⟨x.val, hi (Set.mem_image_of_mem Subtype.val hx)⟩, rfl⟩

end Subsemiring
