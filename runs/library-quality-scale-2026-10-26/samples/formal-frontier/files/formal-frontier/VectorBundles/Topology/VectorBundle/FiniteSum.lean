/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.Algebra.Monoid

/-!
# Locally finite sums of continuous sections

A family of continuous sections of a vector bundle with locally finite nonzero loci has a
continuous fiberwise `finsum`. No norm on the individual fibers is needed.

The proof follows Mathlib's `continuous_finsum`: near each point only finitely many terms
contribute. Continuity of their sum is checked in a local linear trivialization, using
`FiberBundle.continuousAt_section`.

## References

* Mathlib's `continuous_finsum` and `FiberBundle.continuousAt_section`.
-/

@[expose] public section

open Bundle Filter Set Topology

namespace VectorBundle

universe u𝕜 uB uF uE uι

variable (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type uE} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {ι : Type uι} {s : ι → ∀ b, E b}

include 𝕜 in
/-- The fiberwise finite sum of a family of continuous sections is continuous if the
nonzero loci of the sections form a locally finite family. Local finiteness ensures that
near each point the `finsum` is an ordinary sum over a fixed finite set of indices.

This is the vector-bundle counterpart of Mathlib's `continuous_finsum`. -/
theorem continuous_finsum_section
    (hs : ∀ i, Continuous (fun b ↦ (⟨b, s i b⟩ : TotalSpace F E)))
    (hlf : LocallyFinite fun i ↦ {b | s i b ≠ 0}) :
    Continuous (fun b ↦ (⟨b, ∑ᶠ i, s i b⟩ : TotalSpace F E)) := by
  classical
  refine continuous_iff_continuousAt.2 fun b₀ ↦ ?_
  rw [FiberBundle.continuousAt_section]
  let e := trivializationAt F E b₀
  obtain ⟨U, hU, hfin⟩ := hlf b₀
  let I := hfin.toFinset
  have hcoords : ContinuousAt (fun b ↦ ∑ i ∈ I, (e ⟨b, s i b⟩).2) b₀ :=
    tendsto_finsetSum I fun i _ ↦
      (FiberBundle.continuousAt_section F b₀).mp (hs i).continuousAt
  apply hcoords.congr_of_eventuallyEq
  filter_upwards [hU, e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F E b₀)]
    with b hb hbe
  have hsupport : Function.support (fun i ↦ s i b) ⊆ I := by
    intro i hi
    exact hfin.mem_toFinset.mpr ⟨b, hi, hb⟩
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  exact map_sum ((e.linear 𝕜 hbe).mk' _) (fun i ↦ s i b) I

end VectorBundle
