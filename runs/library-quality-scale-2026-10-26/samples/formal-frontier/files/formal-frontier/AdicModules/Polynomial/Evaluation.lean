/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Associated polynomial values at nearby arguments

If `I` lies in the Jacobson radical and `b - a ∈ (g(a)) I`, then `g(b)` and `g(a)`
are associated in the coefficient ring. Applying this to `g = f.derivative` gives
stability of the derivative up to a unit without requiring that derivative to be a unit.

The condition on `I` makes elements of `1 + I` units. Together with polynomial evaluation
congruence, this avoids cancelling `g(a)` and includes zero values, zero divisors and the
zero ring. No Henselian or completeness hypothesis is involved.

## References

The derivative application is motivated by the small-error Hensel argument in
I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition
(2002), II, §1, Corollary 3. This module concerns only association of polynomial values,
not root existence or that whole corollary.

The formulation uses Mathlib's `Polynomial.sub_dvd_eval_sub` (Chris Hughes, Johannes Hölzl,
Kim Morrison and Jens Wagemaker's polynomial division API) and the Jacobson radical API
of Kenny Lau, Devon Tuma and Wojciech Nawrocki.
-/

@[expose] public section

universe u

namespace Polynomial

variable {R : Type u} [CommRing R]

/-- Polynomial values at `a` and `b` are associated when `b - a` belongs to
`Ideal.span {g.eval a} * I` and `I` lies in the Jacobson radical of the coefficient ring.

In particular, use `g = f.derivative` to compare derivative values. The association is
in `R` itself, not in a fraction field, and permits `g.eval a = 0`. The Jacobson condition
ensures that the multiplicative correction is a unit; no cancellation is required. -/
theorem associated_eval_of_sub_mem_span_mul (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) (g : R[X]) (a b : R)
    (hab : b - a ∈ Ideal.span {g.eval a} * I) :
    Associated (g.eval b) (g.eval a) := by
  obtain ⟨i, hi, hiab⟩ := Ideal.mem_span_singleton_mul.mp hab
  obtain ⟨q, hq⟩ := sub_dvd_eval_sub b a g
  have hmul : g.eval b = g.eval a * (1 + i * q) := by
    calc
      g.eval b = (g.eval b - g.eval a) + g.eval a := by ring
      _ = (b - a) * q + g.eval a := by rw [hq]
      _ = (g.eval a * i) * q + g.eval a := by rw [← hiab]
      _ = g.eval a * (1 + i * q) := by ring
  have hu : IsUnit (1 + i * q) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    simpa only [add_sub_cancel_left] using hI (I.mul_mem_right q hi)
  rw [hmul]
  exact associated_mul_unit_left _ _ hu

end Polynomial
