/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.FractionRing
public import QuadraticAlgebras.Integral
public import QuadraticAlgebras.Squarefree
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Integral closure of squarefree quadratic algebras

A domain quadratic algebra `A[ω]` with `ω² = f` is integrally closed when
`A` is a unique factorization domain, `f` is squarefree, and `2` is
invertible.  The proof transports an integral element of the total fraction
ring to the coordinate model over `FractionRing A`.  Its trace and norm
descend to `A`; the trace recovers the constant coordinate, and squarefree
denominator descent recovers the linear coordinate.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft), Exercise 5.4.H, supplies the trace, norm and squarefree
  denominator proof route used for this direction of the criterion.
-/

public section

set_option warningAsError true

noncomputable section

namespace QuadraticAlgebra

universe u

variable {A : Type u} [CommRing A] [IsDomain A]
  [UniqueFactorizationMonoid A] [Invertible (2 : A)]
  {f : A}

/-- A domain quadratic algebra with squarefree radicand over a UFD is
integrally closed when `2` is invertible. The trace/norm and reduced-denominator
argument follows Vakil, *The Rising Sea*, Exercise 5.4.H. -/
theorem isIntegrallyClosed_of_squarefree (hf : Squarefree f)
    [IsDomain (QuadraticAlgebra A f 0)] :
    IsIntegrallyClosed (QuadraticAlgebra A f 0) := by
  rw [isIntegrallyClosed_iff (FractionRing (QuadraticAlgebra A f 0))]
  intro x hx
  let e := fractionRingEquivBaseChange f 0
  let y := e x
  have hy : IsIntegral A y := by
    exact (isIntegral_trans x hx).map e.toAlgHom
  have htrace := isInteger_trace_of_isIntegral hy
  have hnorm := isInteger_norm_of_isIntegral hy
  obtain ⟨t, ht⟩ := htrace
  have hre : IsLocalization.IsInteger A y.re := by
    refine ⟨⅟ (2 : A) * t, ?_⟩
    change algebraMap A (FractionRing A) (⅟ (2 : A) * t) = y.re
    rw [map_mul, ht]
    simp only [trace_def, map_zero, zero_mul, add_zero]
    rw [show (2 : FractionRing A) =
      algebraMap A (FractionRing A) (2 : A) by
        exact (map_ofNat (algebraMap A (FractionRing A)) 2).symm]
    rw [← mul_assoc, ← map_mul, invOf_mul_self, map_one, one_mul]
  obtain ⟨r, hr⟩ := hre
  obtain ⟨n, hn⟩ := hnorm
  have him_sq :
      IsLocalization.IsInteger A
        (y.im ^ 2 * algebraMap A (FractionRing A) f) := by
    refine ⟨r ^ 2 - n, ?_⟩
    rw [map_sub, map_pow, hr, hn]
    simp only [norm_def, map_zero, zero_mul, add_zero]
    ring
  have him : IsLocalization.IsInteger A y.im :=
    IsFractionRing.isInteger_of_sq_mul_squarefree hf him_sq
  obtain ⟨s, hs⟩ := him
  refine ⟨QuadraticAlgebra.mk r s, ?_⟩
  apply e.injective
  rw [fractionRingEquivBaseChange_algebraMap]
  ext
  · exact hr
  · exact hs

end QuadraticAlgebra
