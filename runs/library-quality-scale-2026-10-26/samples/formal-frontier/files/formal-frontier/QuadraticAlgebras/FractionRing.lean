/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.AdjoinRoot
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Fraction rings of quadratic algebras

This file identifies the total fraction ring of a quadratic algebra with its
scalar extension to the total fraction ring of the base.  The key observation
is that a regular quadratic element `x` becomes a scalar regular element after
multiplication by `star x`, since `x * star x` is its norm.

The results hold for arbitrary commutative rings, including rings with zero
divisors and the zero ring.  No domain or irreducibility hypothesis is needed
until a downstream application asks for one of the fraction rings to be a
field.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft), Exercise 5.4.H, motivates the passage to fractions in the
  integral-closure argument; the equivalence here also covers zero divisors.
* Mathlib's [localization base change](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/Localization/BaseChange.lean)
  supplies the scalar-extension localization API.
-/

public section

set_option warningAsError true

noncomputable section

namespace QuadraticAlgebra

universe u v

variable {R : Type u} [CommRing R]

open nonZeroDivisors
open scoped TensorProduct

/-- Scalar extension commutes with the coordinate model of a quadratic
algebra. -/
@[expose]
noncomputable def baseChangeEquiv
    (S : Type v) [CommRing S] [Algebra R S] (a b : R) :
    S ⊗[R] QuadraticAlgebra R a b ≃ₐ[S]
      QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b) := by
  let f : QuadraticAlgebra R a b →ₐ[R]
      QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b) :=
    QuadraticAlgebra.lift ⟨omega, by
      ext <;> simp [Algebra.algebraMap_eq_smul_one]⟩
  let g : QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b) →ₐ[S]
      S ⊗[R] QuadraticAlgebra R a b :=
    QuadraticAlgebra.lift ⟨1 ⊗ₜ[R] omega, by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        omega_mul_omega_eq_algebraMap]
      calc
        1 ⊗ₜ[R] ((algebraMap R (QuadraticAlgebra R a b)) a +
            (algebraMap R (QuadraticAlgebra R a b)) b * omega) =
            1 ⊗ₜ[R] (algebraMap R (QuadraticAlgebra R a b)) a +
              (1 ⊗ₜ[R] (algebraMap R (QuadraticAlgebra R a b)) b) *
                (1 ⊗ₜ[R] omega) := by
                  rw [TensorProduct.tmul_add,
                    Algebra.TensorProduct.tmul_mul_tmul]
                  simp
        _ = (algebraMap R S) a ⊗ₜ[R] 1 +
              ((algebraMap R S) b ⊗ₜ[R] 1) * (1 ⊗ₜ[R] omega) := by
              rw [Algebra.TensorProduct.tmul_one_eq_one_tmul,
                Algebra.TensorProduct.tmul_one_eq_one_tmul]
        _ = (algebraMap R S) a ⊗ₜ[R] 1 +
              (algebraMap R S) b ⊗ₜ[R] omega := by
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        _ = (algebraMap R S) a • 1 +
              (algebraMap R S) b • (1 ⊗ₜ[R] omega) := by
              simp only [algebraMap_smul]
              change
                (algebraMap R S) a ⊗ₜ[R] 1 +
                    (algebraMap R S) b ⊗ₜ[R] omega =
                  (a • (1 : S)) ⊗ₜ[R] 1 + (b • (1 : S)) ⊗ₜ[R] omega
              simp only [← Algebra.algebraMap_eq_smul_one]⟩
  exact AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId S _) f fun _ _ ↦ .all _ _)
    g
    (by
      apply QuadraticAlgebra.algHom_ext
      simp [f, g])
    (by
      ext
      all_goals simp [f, g])

/-- On a pure tensor, base change maps both coordinates into `S` and then
multiplies by the left scalar. No domain assumption is needed. -/
@[simp]
theorem baseChangeEquiv_tmul
    (S : Type v) [CommRing S] [Algebra R S] (a b : R)
    (s : S) (x : QuadraticAlgebra R a b) :
    baseChangeEquiv S a b (s ⊗ₜ[R] x) =
      s • (QuadraticAlgebra.mk
        (algebraMap R S x.re) (algebraMap R S x.im) :
          QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) := by
  have h (r : R) :
      algebraMap R
          (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) r =
        algebraMap S _ (algebraMap R S r) :=
    IsScalarTower.algebraMap_apply R S _ r
  ext <;> simp [baseChangeEquiv, Algebra.smul_def, mul_comm, h]

/-- Base change sends `1 ⊗ omega` to the distinguished quadratic generator. -/
@[simp]
theorem baseChangeEquiv_omega
    (S : Type v) [CommRing S] [Algebra R S] (a b : R) :
    baseChangeEquiv S a b
      (1 ⊗ₜ[R] (omega : QuadraticAlgebra R a b)) =
        (omega : QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) := by
  simp [baseChangeEquiv]

/-- Base change sends `s ⊗ 1` to the scalar `s` in the target quadratic algebra. -/
@[simp]
theorem baseChangeEquiv_tmul_one
    (S : Type v) [CommRing S] [Algebra R S] (a b : R) (s : S) :
    baseChangeEquiv S a b
      (s ⊗ₜ[R] (1 : QuadraticAlgebra R a b)) = algebraMap S _ s := by
  simp [baseChangeEquiv]

/-- Extending scalars from `R` to its total fraction ring already inverts every
regular element of a quadratic algebra. -/
theorem isLocalization_tensor_fractionRing (a b : R) :
    IsLocalization
      (QuadraticAlgebra R a b)⁰
      (QuadraticAlgebra R a b ⊗[R] FractionRing R) := by
  apply IsLocalization.isLocalization_of_is_exists_mul_mem
    (QuadraticAlgebra R a b ⊗[R] FractionRing R)
    (Algebra.algebraMapSubmonoid (QuadraticAlgebra R a b) R⁰)
    (QuadraticAlgebra R a b)⁰
  · rintro _ ⟨r, hr, rfl⟩
    exact algebraMap_mem_nonZeroDivisors_iff.mpr hr
  · intro x
    refine ⟨star x.1, ?_⟩
    rw [mul_comm, ← algebraMap_norm_eq_mul_star]
    exact Algebra.mem_algebraMapSubmonoid_of_mem
      ⟨norm x.1, norm_mem_nonZeroDivisors_iff.mpr x.2⟩

/-- The total fraction ring of a quadratic algebra is its scalar localization
at the regular elements of the base ring. -/
@[expose]
noncomputable def fractionRingEquivTensor (a b : R) :
    FractionRing (QuadraticAlgebra R a b) ≃ₐ[QuadraticAlgebra R a b]
      QuadraticAlgebra R a b ⊗[R] FractionRing R := by
  letI := isLocalization_tensor_fractionRing a b
  exact FractionRing.algEquiv
    (QuadraticAlgebra R a b)
    (QuadraticAlgebra R a b ⊗[R] FractionRing R)

/-- The total-fraction-ring equivalence agrees with the canonical algebra map
on elements of the original quadratic algebra. -/
@[simp]
theorem fractionRingEquivTensor_algebraMap
    (a b : R) (x : QuadraticAlgebra R a b) :
    fractionRingEquivTensor a b
      (algebraMap (QuadraticAlgebra R a b)
        (FractionRing (QuadraticAlgebra R a b)) x) =
      algebraMap (QuadraticAlgebra R a b)
        (QuadraticAlgebra R a b ⊗[R] FractionRing R) x := by
  simp [fractionRingEquivTensor]

/-- Coordinate form of the total fraction ring of a quadratic algebra after
extending the two defining coefficients to `FractionRing R`. -/
@[expose]
noncomputable def fractionRingEquivBaseChange (a b : R) :
    FractionRing (QuadraticAlgebra R a b) ≃ₐ[R]
      QuadraticAlgebra (FractionRing R)
        (algebraMap R (FractionRing R) a) (algebraMap R (FractionRing R) b) :=
  ((fractionRingEquivTensor a b).restrictScalars R) |>.trans
    (Algebra.TensorProduct.comm R (QuadraticAlgebra R a b) (FractionRing R)) |>.trans
    ((baseChangeEquiv (FractionRing R) a b).restrictScalars R)

/-- An original quadratic element maps to the pair of its coordinates in
`FractionRing R` under the total-fraction-ring/base-change equivalence. -/
@[simp]
theorem fractionRingEquivBaseChange_algebraMap
    (a b : R) (x : QuadraticAlgebra R a b) :
    fractionRingEquivBaseChange a b
      (algebraMap (QuadraticAlgebra R a b)
        (FractionRing (QuadraticAlgebra R a b)) x) =
      QuadraticAlgebra.mk
        (algebraMap R (FractionRing R) x.re)
        (algebraMap R (FractionRing R) x.im) := by
  have h (r : R) :
      algebraMap R
          (QuadraticAlgebra (FractionRing R)
            (algebraMap R (FractionRing R) a)
            (algebraMap R (FractionRing R) b)) r =
        algebraMap (FractionRing R) _ (algebraMap R (FractionRing R) r) :=
    IsScalarTower.algebraMap_apply R (FractionRing R) _ r
  ext <;> simp [fractionRingEquivBaseChange,
    fractionRingEquivTensor, baseChangeEquiv, Algebra.smul_def, h]

/-- The base-change presentation of the total fraction ring preserves `omega`. -/
@[simp]
theorem fractionRingEquivBaseChange_omega (a b : R) :
    fractionRingEquivBaseChange a b
      (algebraMap (QuadraticAlgebra R a b)
        (FractionRing (QuadraticAlgebra R a b)) omega) =
      (omega : QuadraticAlgebra (FractionRing R)
        (algebraMap R (FractionRing R) a) (algebraMap R (FractionRing R) b)) := by
  simp [fractionRingEquivBaseChange, fractionRingEquivTensor, baseChangeEquiv]

/-- Polynomial-quotient form of the total fraction ring of a quadratic
algebra. -/
@[expose]
noncomputable def fractionRingEquivAdjoinRoot (a b : R) :
    FractionRing (QuadraticAlgebra R a b) ≃ₐ[R]
      AdjoinRoot (definingPolynomial
        (algebraMap R (FractionRing R) a) (algebraMap R (FractionRing R) b)) :=
  (fractionRingEquivBaseChange a b).trans
    ((equivAdjoinRoot
      (algebraMap R (FractionRing R) a)
      (algebraMap R (FractionRing R) b)).restrictScalars R)

/-- The quotient presentation of the total fraction ring sends the embedded
`omega` to the root of the quadratic with fraction-ring coefficients. -/
@[simp]
theorem fractionRingEquivAdjoinRoot_omega (a b : R) :
    fractionRingEquivAdjoinRoot a b
      (algebraMap (QuadraticAlgebra R a b)
        (FractionRing (QuadraticAlgebra R a b)) omega) =
      AdjoinRoot.root (definingPolynomial
        (algebraMap R (FractionRing R) a) (algebraMap R (FractionRing R) b)) := by
  rw [fractionRingEquivAdjoinRoot, AlgEquiv.trans_apply,
    fractionRingEquivBaseChange_omega]
  change
    equivAdjoinRoot
      (algebraMap R (FractionRing R) a)
      (algebraMap R (FractionRing R) b) omega = _
  exact equivAdjoinRoot_apply_omega _ _

end QuadraticAlgebra
