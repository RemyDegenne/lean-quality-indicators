/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.SModEq.Pow

/-!
# Iterated powers and ideal-power congruences

An ideal containing a natural number `q` gains one power of precision each time
congruent elements at positive depth are raised to the `q`-th power.

## References

The bound generalizes Fesenko–Vostokov, *Local Fields and Their Extensions*,
second edition, I §7, Lemma (7.2), from a discrete valuation ring and its residue
characteristic to an arbitrary commutative ring and a natural number in an ideal.
It extends Kenny Lau's `SModEq.pow_pow_add_one` in Mathlib from starting depth
one to arbitrary positive starting depth. The one-step arithmetic is provided
by Mathlib's `SModEq.pow_add_one`.
-/

@[expose] public section

universe u

namespace SModEq

/-- If `(q : R) ∈ I`, iterated `q`-th powers improve a congruence modulo `I ^ m`
to one modulo `I ^ (m + n)`, provided the starting depth `m` is positive.

No primality assumption on `q` is needed; in particular `q = 0` and `q = 1`
are allowed under the same ideal-membership hypothesis. This generalizes the
valuation bound in Fesenko–Vostokov, I §7, Lemma (7.2). -/
theorem pow_pow_add {R : Type u} [CommRing R] {I : Ideal R} {q m : ℕ} {x y : R}
    (hqI : (q : R) ∈ I) (hm : m ≠ 0) (h : x ≡ y [SMOD I ^ m]) (n : ℕ) :
    x ^ (q ^ n) ≡ y ^ (q ^ n) [SMOD I ^ (m + n)] := by
  induction n with
  | zero => simpa only [pow_zero, pow_one, Nat.add_zero] using h
  | succ n ih =>
    have hmn : m + n ≠ 0 := (Nat.add_pos_left (Nat.pos_of_ne_zero hm) n).ne'
    simpa only [pow_succ q n, pow_mul, Nat.add_succ] using ih.pow_add_one hqI hmn

end SModEq
