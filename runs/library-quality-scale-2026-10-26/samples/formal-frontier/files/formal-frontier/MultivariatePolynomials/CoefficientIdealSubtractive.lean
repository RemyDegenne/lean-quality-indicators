/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.CoefficientIdeal
public import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Tactic.Ring

/-!
# Subtractivity from a radical polynomial extension

If the extension of a coefficient ideal to a polynomial semiring with at least
one variable is radical, then membership of `a` and `a + b` forces membership of
`b`. For a variable `X`, the square of
`P = C a + C b * X + C (a + b) * X ^ 2` belongs to the extended ideal:
it is a sum of multiples of `C a` and `C (a + b)`. Radicality puts `P` in the
ideal, and its linear coefficient is `b`. The prime-extension statement follows
because prime ideals are radical.

The nonempty variable hypothesis is essential. In the natural numbers, the
ideal consisting of zero and all numbers at least two is prime: its complement
is the multiplicatively closed singleton containing one. This ideal contains
two and three but not one. With no variables, the constant map is an
isomorphism, so the extension of this ideal is still prime and hence radical.

## References

* `MultivariatePolynomials.CoefficientIdeal` for
  `MvPolynomial.mem_map_C_iff_coeff_mem`.
* Mathlib's `AddMonoidAlgebra.coeff_add` and the coefficient lemmas in
  `Mathlib.Algebra.MvPolynomial.Basic`.
* `Mathlib.RingTheory.Ideal.Operations` for `Ideal.IsRadical` and
  `Ideal.IsPrime.isRadical`.
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- A radical extension to polynomials in a nonempty variable type forces
subtraction of ideal membership: if `a` and `a + b` lie in the coefficient
ideal, then so does `b`. -/
theorem mem_of_add_mem_of_isRadical_map_C {R : Type u} {σ : Type v}
    [CommSemiring R] [Nonempty σ] (I : Ideal R)
    (h : (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)).IsRadical)
    {a b : R} (ha : a ∈ I) (hab : a + b ∈ I) : b ∈ I := by
  classical
  obtain ⟨j⟩ := ‹Nonempty σ›
  let J : Ideal (MvPolynomial σ R) := I.map (C : R →+* MvPolynomial σ R)
  let P : MvPolynomial σ R := C a + C b * X j + C (a + b) * X j ^ 2
  have haC : C a ∈ J := Ideal.mem_map_of_mem C ha
  have habC : C (a + b) ∈ J := Ideal.mem_map_of_mem C hab
  have hsquare :
      P ^ 2 =
        C a * (C a + C (b + b) * X j + C (a + a + b) * X j ^ 2) +
          C (a + b) *
            (C b * X j ^ 2 + C (b + b) * X j ^ 3 + C (a + b) * X j ^ 4) := by
    dsimp only [P]
    simp only [map_add]
    ring
  have hP2 : P ^ 2 ∈ J := by
    rw [hsquare]
    exact J.add_mem (J.mul_mem_right _ haC) (J.mul_mem_right _ habC)
  have hP : P ∈ J := h ⟨2, hP2⟩
  have h01 : (0 : σ →₀ ℕ) ≠ Finsupp.single j 1 := by
    intro heq
    simpa using congrArg (fun d : σ →₀ ℕ => d j) heq
  have h21 : (Finsupp.single j 2 : σ →₀ ℕ) ≠ Finsupp.single j 1 := by
    intro heq
    simpa using congrArg (fun d : σ →₀ ℕ => d j) heq
  have hcoeff : P.coeff (Finsupp.single j 1) = b := by
    dsimp only [P]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C, if_neg h01,
      coeff_C_mul, coeff_X_same, coeff_X_pow, if_neg h21, mul_one, mul_zero,
      zero_add, add_zero]
  simpa only [hcoeff] using (mem_map_C_iff_coeff_mem.mp hP) (Finsupp.single j 1)

/-- A prime extension to polynomials in a nonempty variable type forces
subtraction of ideal membership: if `a` and `a + b` lie in the coefficient
ideal, then so does `b`. -/
theorem mem_of_add_mem_of_isPrime_map_C {R : Type u} {σ : Type v}
    [CommSemiring R] [Nonempty σ] (I : Ideal R)
    (h : (I.map (C : R →+* MvPolynomial σ R)).IsPrime)
    {a b : R} (ha : a ∈ I) (hab : a + b ∈ I) : b ∈ I := by
  exact mem_of_add_mem_of_isRadical_map_C I h.isRadical ha hab

end MvPolynomial
