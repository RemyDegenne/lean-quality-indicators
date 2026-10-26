/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Multiplicity

/-!
# Discrete values of elements admitting roots of all depths

An integer-valued valuation of an element admitting a `q ^ n`-th root for every
natural `n`, with `1 < q`, can only be zero or one. The roots need not form a
compatible tower. The zero case is included, and the ring need not be commutative.

The proof transports roots to divisibility of the integer logarithm of the value.
Mathlib's `FiniteMultiplicity.not_iff_forall` and `Int.finiteMultiplicity_iff`
then force that logarithm to vanish. The zero value is treated separately before
recovering the value from its logarithm. No characteristic or topological
assumptions are needed.

## References

The integer power-divisibility argument uses Mathlib's multiplicity theory, and
the valuation bridge uses its `WithZero.log_pow`, `exp_log` and `exp_zero`.
-/

@[expose] public section

universe u

open scoped WithZero

namespace Valuation

/-- An element admitting roots of every depth along powers of `q > 1` has value
zero or one under an integer-valued valuation. No compatibility between the roots
is required. -/
theorem eq_zero_or_eq_one_of_forall_exists_pow_eq {R : Type u} [Ring R]
    (v : Valuation R ℤᵐ⁰) (q : ℕ) (hq : 1 < q) (x : R)
    (hroot : ∀ n : ℕ, ∃ y : R, y ^ (q ^ n) = x) : v x = 0 ∨ v x = 1 := by
  by_cases hx : v x = 0
  · exact Or.inl hx
  right
  have hdiv : ∀ n : ℕ, (q : ℤ) ^ n ∣ WithZero.log (v x) := by
    intro n
    obtain ⟨y, hy⟩ := hroot n
    refine ⟨WithZero.log (v y), ?_⟩
    rw [← hy, map_pow, WithZero.log_pow, nsmul_eq_mul, Nat.cast_pow]
  have hlog : WithZero.log (v x) = 0 := by
    by_contra h
    exact (FiniteMultiplicity.not_iff_forall.mpr hdiv)
      (Int.finiteMultiplicity_iff.mpr ⟨by simpa using (ne_of_gt hq), h⟩)
  rw [← WithZero.exp_log hx, hlog, WithZero.exp_zero]

end Valuation
