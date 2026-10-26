/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Kronecker products of matrix units

Kronecker products of two unit matrices are units over any semiring, without
requiring commutative coefficients. The factorization is in coefficient order:
`(A ⊗ₖ 1) * (1 ⊗ₖ B) = A ⊗ₖ B`. Its rectangular form needs only a
`NonAssocSemiring` and finite, decidable middle indices.

The proof transports units through Mathlib's constant-family, block-diagonal,
and reindexing maps, then multiplies them. Consequently, for chosen input units
with inverse values `A'` and `B'`, the inverse witness is the reversed product
`(1 ⊗ₖ B') * (A' ⊗ₖ 1)`, not in general `A' ⊗ₖ B'`.

Over a commutative semiring, the unit extracted from this result agrees with
Mathlib's `Matrix.GeneralLinearGroup.kronecker`.

## References

* Mathlib's `Matrix.IsUnit.kronecker` and `Matrix.GeneralLinearGroup.kronecker`
  provide the commutative-coefficient unit theorem and construction.
* The proofs follow Mathlib's Kronecker, block-matrix, reindexing, constant-family,
  and `Units` formalizations.
-/

set_option warningAsError true

@[expose] public section

universe u v w u₁ u₂ u₃ u₄

namespace Matrix

/-- Multiplying the two identity-factor Kronecker products gives the Kronecker
product in coefficient order. Only the middle indices need to be finite and
have decidable equality; the outer indices are unrestricted. -/
theorem kronecker_one_mul_one_kronecker
    {ℓ : Type u₁} {d : Type u₂} {s : Type u₃} {p : Type u₄} {R : Type w}
    [Fintype d] [DecidableEq d] [Fintype s] [DecidableEq s] [NonAssocSemiring R]
    (A : Matrix ℓ d R) (B : Matrix s p R) :
    Matrix.kronecker A (1 : Matrix s s R) *
        Matrix.kronecker (1 : Matrix d d R) B = Matrix.kronecker A B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    ← Finset.univ_product_univ, Finset.sum_product]
  rw [Fintype.sum_eq_single j]
  · rw [Fintype.sum_eq_single a]
    · simp
    · intro a' ha'
      simp [Ne.symm ha']
  · intro j' hj'
    apply Finset.sum_eq_zero
    intro a' _
    simp [Matrix.one_apply, hj']

private theorem isUnit_blockDiagonal_const
    {n : Type u} {m : Type v} {R : Type w}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Semiring R]
    {A : Matrix n n R} (hA : IsUnit A) :
    IsUnit (Matrix.blockDiagonal fun _ : m => A) := by
  exact (hA.map (Pi.constMonoidHom m (Matrix n n R))).map
    (Matrix.blockDiagonalRingHom (m := n) (o := m) (α := R))

/-- The Kronecker product of two unit matrices is a unit over a possibly
noncommutative semiring. This generalizes Mathlib's `Matrix.IsUnit.kronecker`
from commutative coefficients. No nonempty-index or nontrivial-coefficient
assumption is needed. -/
theorem isUnit_kronecker
    {n : Type u} {m : Type v} {R : Type w}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Semiring R]
    {A : Matrix n n R} {B : Matrix m m R} (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (Matrix.kronecker A B) := by
  have hLeft : IsUnit (Matrix.kronecker A (1 : Matrix m m R)) := by
    simpa only [Matrix.kronecker, Matrix.kronecker_one] using
      (isUnit_blockDiagonal_const (m := m) hA)
  have hRight : IsUnit (Matrix.kronecker (1 : Matrix n n R) B) := by
    simpa only [Matrix.kronecker, Matrix.one_kronecker, Matrix.coe_reindexRingEquiv] using
      (isUnit_blockDiagonal_const (m := n) hB).map
        (Matrix.reindexRingEquiv R (Equiv.prodComm m n))
  rw [← kronecker_one_mul_one_kronecker A B]
  exact hLeft.mul hRight

/-- Over commutative coefficients, extracting a unit from the semiring result
agrees with the stock general-linear-group Kronecker construction. This is an
equality of units, whose inverse data are determined by their common value. -/
theorem GeneralLinearGroup.isUnit_kronecker_unit
    {n : Type u} {m : Type v} {R : Type w}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [CommSemiring R]
    (x : GeneralLinearGroup n R) (y : GeneralLinearGroup m R) :
    (Matrix.isUnit_kronecker
      (A := (x : Matrix n n R)) (B := (y : Matrix m m R)) x.isUnit y.isUnit).unit =
        GeneralLinearGroup.kronecker x y := by
  apply Units.ext
  exact (Matrix.isUnit_kronecker x.isUnit y.isUnit).unit_spec

end Matrix
