/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Repeated diagonal blocks

This file defines the operation that repeats a rectangular matrix on diagonal
blocks. For square matrices, it packages that operation as an injective ring
homomorphism whenever the finite block-indexing type is nonempty.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Exercise I.1.13(e) (matrix stabilization by repeated diagonal blocks).
* Mathlib, `Data.Matrix.Block` and `LinearAlgebra.Matrix.Kronecker`
  (block diagonal matrices and Kronecker products used in this construction).
-/

set_option warningAsError true

@[expose] public section

open scoped Kronecker

universe u v w x

namespace Matrix

variable {R : Type u} [NonAssocSemiring R]

section Rectangular

variable {m : Type v} {n : Type w} {o : Type x} [DecidableEq o]

/-- Repeat a rectangular matrix on diagonal blocks indexed by `o`. -/
def repeatBlock (A : Matrix m n R) : Matrix (m × o) (n × o) R :=
  blockDiagonal (fun _ : o => A)

/-- Repeated diagonal blocks are the Kronecker product with an identity
matrix. -/
theorem repeatBlock_eq_kronecker_one (A : Matrix m n R) :
    repeatBlock (o := o) A = A ⊗ₖ (1 : Matrix o o R) := by
  exact (kronecker_one (n := o) A).symm

end Rectangular

section Square

variable {m : Type v} {o : Type w}
variable [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]

/-- Repeat a square matrix on diagonal blocks, as a ring homomorphism. -/
def repeatBlockHom : Matrix m m R →+* Matrix (m × o) (m × o) R :=
  (blockDiagonalRingHom (α := R) (m := m) (o := o)).comp
    (Pi.constRingHom o (Matrix m m R))

@[simp]
theorem repeatBlockHom_apply (A : Matrix m m R) :
    repeatBlockHom (R := R) (m := m) (o := o) A = repeatBlock (o := o) A :=
  rfl

/-- The repeated-block ring homomorphism is exactly Kronecker product with an
identity matrix. -/
theorem repeatBlockHom_apply_eq_kronecker_one (A : Matrix m m R) :
    repeatBlockHom (R := R) (m := m) (o := o) A =
      A ⊗ₖ (1 : Matrix o o R) := by
  rw [repeatBlockHom_apply, repeatBlock_eq_kronecker_one]

/-- Repeating square matrices on a nonempty family of diagonal blocks is
injective. -/
theorem repeatBlockHom_injective [Nonempty o] :
    Function.Injective (repeatBlockHom (R := R) (m := m) (o := o)) := by
  intro A B h
  change blockDiagonal (fun _ : o => A) =
    blockDiagonal (fun _ : o => B) at h
  exact Function.const_injective (blockDiagonal_injective h)

end Square

end Matrix
