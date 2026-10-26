/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Basic
public import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.BigOperators.Pi

/-!
# Stable range of dependent products

The stable-range condition for a dependent product of rings follows from the
condition in each factor, for any index type and row length.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Exercise I.1.5 (the stable-range condition applied componentwise).
* Mathlib, `Algebra.Ring.Pi` and `Algebra.BigOperators.Pi` (dependent
  product rings and coordinatewise finite sums).
-/

set_option warningAsError true

@[expose] public section

namespace Bass

universe u v

/-- A dependent product satisfies `(Sₙ)` when each of its component rings does. -/
theorem stableRangeCondition_pi
    {ι : Type u} {S : ι → Type v} [∀ i, Ring (S i)] {n : ℕ}
    (h : ∀ i, StableRangeCondition (S i) n) :
    StableRangeCondition (∀ i, S i) n := by
  classical
  intro r0 r hr
  obtain ⟨s0, s, hs⟩ := hr
  have hr_i (i : ι) : IsRightUnimodularCons (r0 i) (fun j ↦ r j i) := by
    refine ⟨s0 i, fun j ↦ s j i, ?_⟩
    simpa only [Pi.add_apply, Pi.mul_apply, Pi.one_apply, Finset.sum_apply] using
      congrFun hs i
  choose t ht using fun i ↦ h i (r0 i) (fun j ↦ r j i) (hr_i i)
  choose w hw using ht
  refine ⟨fun j i ↦ t i j, fun j i ↦ w i j, ?_⟩
  funext i
  simpa only [Finset.sum_apply, Pi.sub_apply, Pi.mul_apply, Pi.one_apply] using hw i

end Bass
