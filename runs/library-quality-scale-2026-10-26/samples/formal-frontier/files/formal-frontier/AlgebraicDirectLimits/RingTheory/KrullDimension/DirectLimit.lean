/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.RingTheory.DirectLimit
public import AlgebraicDirectLimits.RingTheory.KrullDimension.FiniteCapture
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Krull dimension of directed colimits

The Krull dimension of a directed colimit of commutative semirings is at most the
supremum of the stage dimensions. Transition homomorphisms need not be injective.
The dimension takes values in `WithBot ℕ∞`, including the empty-spectrum value `⊥`
and infinite dimension `⊤`.

The finite-subset criterion is `ringKrullDim_le_iSup_of_finite_subset_range`.
The characteristic maps of the colimit are `DirectLimit.Ring.of`. Their ranges
form a directed cover, so every finite subset is contained in one stage range.
Nonemptiness supplies a stage even for the empty finite subset.

## References

The proof uses Mathlib's representative API `DirectLimit.exists_eq_mk`, the
characteristic-map equation `DirectLimit.Ring.of_f`, and its directed finite-union
capture lemma `Directed.exists_mem_subset_of_finset_subset_biUnion`. The dimension
bound is the finite-subset criterion in this library.
-/

@[expose] public section

universe u v

/-- The Krull dimension of a nonempty directed colimit of commutative semirings
is at most the supremum of the stage dimensions. The index and stage-value
universes are independent, and no injectivity is assumed. -/
theorem ringKrullDim_directLimit_le_iSup
    {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (G : ι → Type v) [∀ i, CommSemiring (G i)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (f · · ·)] :
    ringKrullDim (DirectLimit G f) ≤ ⨆ i, ringKrullDim (G i) := by
  classical
  apply ringKrullDim_le_iSup_of_finite_subset_range (DirectLimit.Ring.of G f)
  intro E hE
  have hdir : Directed (· ⊆ ·) (fun i => Set.range (DirectLimit.Ring.of G f i)) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨f i k hik x, DirectLimit.Ring.of_f hik x⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨f j k hjk x, DirectLimit.Ring.of_f hjk x⟩
  have hcover : E ⊆ ⋃ i, Set.range (DirectLimit.Ring.of G f i) := by
    intro z _
    obtain ⟨i, x, hx⟩ := DirectLimit.exists_eq_mk f z
    exact Set.mem_iUnion.mpr ⟨i, x, hx.symm⟩
  simpa only [hE.coe_toFinset] using
    hdir.exists_mem_subset_of_finset_subset_biUnion
      (s := hE.toFinset) (by simpa only [hE.coe_toFinset] using hcover)
