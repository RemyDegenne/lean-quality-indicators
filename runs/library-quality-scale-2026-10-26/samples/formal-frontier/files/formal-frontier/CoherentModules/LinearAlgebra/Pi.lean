/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Ideal multiples of dependent products

Multiplication by a finitely generated ideal commutes with arbitrary dependent
products of submodules. Finite generation gives a single finite family of scalar
generators, while the module coefficients may be chosen independently in every
coordinate. The index type need not be finite.

## References

The construction uses Mathlib's finite generating families, ideal multiples of
spans, and dependent products of submodules.
-/

@[expose] public section

open scoped Pointwise

universe u v w

namespace Submodule

/-- Multiplication by a finitely generated ideal commutes with the full dependent
product of submodules. The coefficient semiring, index type and module carriers
have independent universes, and empty products are allowed. -/
theorem smul_pi_of_fg
    {R : Type u} [CommSemiring R] {ι : Type v} {M : ι → Type w}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (I : Ideal R) (hI : I.FG) (N : ∀ i, Submodule R (M i)) :
    I • Submodule.pi Set.univ N = Submodule.pi Set.univ (fun i ↦ I • N i) := by
  classical
  refine le_antisymm (smul_le.mpr ?_) ?_
  · intro r hr x hx
    exact mem_pi.mpr fun i hi ↦ smul_mem_smul hr (mem_pi.mp hx i hi)
  · obtain ⟨s, hs⟩ := hI
    intro x hx
    have hx' (i : ι) : x i ∈ (s : Set R) • N i := by
      rw [← coe_span_smul (s : Set R) (N i), coe_set_smul, hs]
      exact mem_pi.mp hx i (Set.mem_univ i)
    choose c hc hxc using fun i ↦ (mem_set_smul (s : Set R) (N i) (x i)).mp (hx' i)
    -- Every coordinate sum can be taken over the same finite set of scalars.
    have hsum (i : ι) : x i = ∑ r ∈ s, r • (c i r : M i) := by
      rw [hxc i,
        Finsupp.sum_of_support_subset (c i) (hc i) (fun r m ↦ r • m)
          (fun r _ ↦ smul_zero r)]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    have hxsum : x = ∑ r ∈ s, r • (fun i ↦ (c i r : M i)) := by
      ext i
      simpa only [Finset.sum_apply, Pi.smul_apply] using hsum i
    rw [hxsum]
    refine Submodule.sum_mem _ fun r hr ↦ smul_mem_smul ?_ ?_
    · rw [← hs]
      exact subset_span hr
    · exact mem_pi.mpr fun i _ ↦ (c i r).property

end Submodule
