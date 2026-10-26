/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.FractionRing
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Repeated-square obstructions to quadratic integral closedness

If a nonzero nonunit square divides the radicand `f`, then `omega / p` is an
integral element of the fraction field of `QuadraticAlgebra A f 0` which does
not belong to the quadratic algebra.  Consequently a domain quadratic algebra
over a unique factorization domain cannot be integrally closed when its
radicand is not squarefree.

The domain hypothesis on the quadratic algebra rules out the zero radicand.
This boundary is essential: an unconditional nonsquarefree-to-prime-square
statement is false for zero in a field with no prime elements.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft), Exercise 5.4.H, supplies the repeated-square obstruction;
  the domain hypothesis and nonzero case are explicit here.
* Mathlib's [integral-closure API](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean)
  provides the fraction-ring characterization of integral closedness.
-/

public section

set_option warningAsError true

noncomputable section

namespace QuadraticAlgebra

universe u

variable {A : Type u} [CommRing A] [IsDomain A]
  {f p : A}

/-- The radicand of a domain quadratic algebra is nonzero. -/
theorem radicand_ne_zero_of_isDomain
    [IsDomain (QuadraticAlgebra A f 0)] : f ≠ 0 := by
  intro hf
  have homega_sq : (omega : QuadraticAlgebra A f 0) ^ 2 = 0 := by
    rw [omega_pow_two_eq_add]
    simp [hf]
  have homega : (omega : QuadraticAlgebra A f 0) = 0 :=
    sq_eq_zero_iff.mp (by simpa [pow_two] using homega_sq)
  have him := congrArg QuadraticAlgebra.im homega
  simp at him

omit [IsDomain A] in
/-- A nonzero nonsquarefree element of a UFD has a prime whose square divides
it. -/
theorem exists_prime_sq_dvd_of_not_squarefree
    [UniqueFactorizationMonoid A]
    (hf0 : f ≠ 0) (hf : ¬ Squarefree f) :
    ∃ p : A, Prime p ∧ p ^ 2 ∣ f := by
  rw [squarefree_iff_no_irreducibles hf0] at hf
  push Not at hf
  obtain ⟨p, hp, hp2⟩ := hf
  exact ⟨p, hp.prime, by simpa [pow_two] using hp2⟩

/-- If a nonzero nonunit square divides the radicand, the fraction `omega / p`
is integral over the quadratic algebra but is not in its image. -/
theorem exists_integral_not_mem_range_of_sq_dvd
    [IsDomain (QuadraticAlgebra A f 0)]
    (hp0 : p ≠ 0) (hp : ¬ IsUnit p) (hpf : p ^ 2 ∣ f) :
    ∃ x : FractionRing (QuadraticAlgebra A f 0),
      IsIntegral (QuadraticAlgebra A f 0) x ∧
        x ∉ Set.range
          (algebraMap (QuadraticAlgebra A f 0)
            (FractionRing (QuadraticAlgebra A f 0))) := by
  obtain ⟨q, hq⟩ := hpf
  have hpB : algebraMap A (QuadraticAlgebra A f 0) p ≠ 0 := by
    simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective A (QuadraticAlgebra A f 0)).ne hp0
  have hpK :
      algebraMap (QuadraticAlgebra A f 0)
          (FractionRing (QuadraticAlgebra A f 0))
          (algebraMap A (QuadraticAlgebra A f 0) p) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (QuadraticAlgebra A f 0)
        (FractionRing (QuadraticAlgebra A f 0))).ne hpB
  let beta : FractionRing (QuadraticAlgebra A f 0) :=
    algebraMap (QuadraticAlgebra A f 0)
        (FractionRing (QuadraticAlgebra A f 0)) omega /
      algebraMap (QuadraticAlgebra A f 0)
        (FractionRing (QuadraticAlgebra A f 0))
        (algebraMap A (QuadraticAlgebra A f 0) p)
  have hmap :
      algebraMap (QuadraticAlgebra A f 0)
          (FractionRing (QuadraticAlgebra A f 0))
          (algebraMap A (QuadraticAlgebra A f 0) f) =
        algebraMap (QuadraticAlgebra A f 0)
            (FractionRing (QuadraticAlgebra A f 0))
            (algebraMap A (QuadraticAlgebra A f 0) p) ^ 2 *
          algebraMap (QuadraticAlgebra A f 0)
            (FractionRing (QuadraticAlgebra A f 0))
            (algebraMap A (QuadraticAlgebra A f 0) q) := by
    simpa only [RingHom.comp_apply, map_mul, map_pow] using
      congrArg
        ((algebraMap (QuadraticAlgebra A f 0)
          (FractionRing (QuadraticAlgebra A f 0))).comp
            (algebraMap A (QuadraticAlgebra A f 0))) hq
  have hbeta_sq :
      beta ^ 2 =
        algebraMap (QuadraticAlgebra A f 0)
          (FractionRing (QuadraticAlgebra A f 0))
          (algebraMap A (QuadraticAlgebra A f 0) q) := by
    dsimp [beta]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hpK)).2
    rw [← map_pow, omega_pow_two_eq_add]
    simp only [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one]
    rw [hmap]
    ring
  refine ⟨beta, ?_, ?_⟩
  · apply IsIntegral.of_pow (by omega : 0 < 2)
    rw [hbeta_sq]
    exact isIntegral_algebraMap
  · rintro ⟨x, hx⟩
    have hcrossK :
        algebraMap (QuadraticAlgebra A f 0)
            (FractionRing (QuadraticAlgebra A f 0)) omega =
          algebraMap (QuadraticAlgebra A f 0)
            (FractionRing (QuadraticAlgebra A f 0))
            (x * algebraMap A (QuadraticAlgebra A f 0) p) := by
      rw [map_mul]
      exact ((eq_div_iff hpK).mp (by simpa [beta] using hx)).symm
    have hcross :
        omega = x * algebraMap A (QuadraticAlgebra A f 0) p :=
      IsFractionRing.injective (QuadraticAlgebra A f 0)
        (FractionRing (QuadraticAlgebra A f 0)) hcrossK
    have him := congrArg QuadraticAlgebra.im hcross
    have him' : (1 : A) = x.im * p := by
      simpa using him
    apply hp
    exact IsUnit.of_mul_eq_one x.im (by simpa [mul_comm] using him'.symm)

/-- A domain quadratic algebra is not integrally closed when its radicand has
a nonzero nonunit square divisor. -/
theorem not_isIntegrallyClosed_of_sq_dvd
    [IsDomain (QuadraticAlgebra A f 0)]
    (hp0 : p ≠ 0) (hp : ¬ IsUnit p) (hpf : p ^ 2 ∣ f) :
    ¬ IsIntegrallyClosed (QuadraticAlgebra A f 0) := by
  obtain ⟨x, hx, hmem⟩ :=
    exists_integral_not_mem_range_of_sq_dvd (f := f) hp0 hp hpf
  intro hclosed
  exact hmem ((isIntegrallyClosed_iff
    (FractionRing (QuadraticAlgebra A f 0))).mp hclosed hx)

/-- A domain quadratic algebra over a UFD is not integrally closed when its
radicand is not squarefree. The integral `omega / p` obstruction follows Vakil,
*The Rising Sea*, Exercise 5.4.H; the domain assumption excludes the zero case. -/
theorem not_isIntegrallyClosed_of_not_squarefree
    [UniqueFactorizationMonoid A]
    [IsDomain (QuadraticAlgebra A f 0)] (hf : ¬ Squarefree f) :
    ¬ IsIntegrallyClosed (QuadraticAlgebra A f 0) := by
  obtain ⟨p, hp, hp2⟩ :=
    exists_prime_sq_dvd_of_not_squarefree
      (radicand_ne_zero_of_isDomain (f := f)) hf
  exact not_isIntegrallyClosed_of_sq_dvd hp.ne_zero hp.not_isUnit hp2

end QuadraticAlgebra
