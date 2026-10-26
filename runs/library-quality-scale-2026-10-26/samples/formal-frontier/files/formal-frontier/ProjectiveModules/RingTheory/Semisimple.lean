/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Chosen matrix decompositions of semisimple rings

`MatrixDivisionDecomposition.{uR, uD} R` retains the data of a finite matrix-ring
decomposition with nonzero block sizes, with coefficient universe independent
of the universe of `R`. Its constructor for a semisimple ring uses Mathlib's
proved Wedderburn–Artin theorem and has coefficients in the same universe as
`R`. The number of factors may be zero, so the zero ring is included. This datum
does not select simple modules from the left-ideal witnesses in the
endomorphism-ring form of that theorem.

## References and credits

* Mathlib's Wedderburn–Artin formalization: the existence of a ring equivalence
  to a finite product of nonempty matrix rings over division rings.
-/

@[expose] public section

universe uR uD

/-- A chosen finite matrix decomposition of a ring, with division coefficients
in an independent universe and positive block sizes. There need not be any
factors. -/
structure MatrixDivisionDecomposition (R : Type uR) [Ring R] where
  /-- The number of matrix factors. -/
  size : ℕ
  /-- The coefficient division rings. -/
  coefficient : Fin size → Type uD
  /-- The sizes of the matrix blocks. -/
  blockSize : Fin size → ℕ
  /-- Each coefficient is a division ring. -/
  [divisionRing : ∀ i, DivisionRing (coefficient i)]
  /-- Every block size is nonzero. -/
  [blockSize_neZero : ∀ i, NeZero (blockSize i)]
  /-- The specified decomposition of the original ring. -/
  ringEquiv : R ≃+* ∀ i, Matrix (Fin (blockSize i)) (Fin (blockSize i)) (coefficient i)

attribute [instance] MatrixDivisionDecomposition.divisionRing
  MatrixDivisionDecomposition.blockSize_neZero

namespace MatrixDivisionDecomposition

variable (R : Type uR) [Ring R]

/-- Mathlib's Wedderburn–Artin theorem supplies the whole decomposition datum,
including division-ring structures and nonzero block-size proofs, with
coefficients in the same universe as the original ring. -/
theorem nonempty_of_isSemisimpleRing [IsSemisimpleRing R] :
    Nonempty (MatrixDivisionDecomposition.{uR, uR} R) := by
  obtain ⟨n, D, d, hD, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  exact ⟨
    { size := n
      coefficient := D
      blockSize := d
      divisionRing := hD
      blockSize_neZero := hd
      ringEquiv := e }⟩

/-- A chosen matrix decomposition of a semisimple ring, with coefficients in
the same universe, selected from Mathlib's proved Wedderburn–Artin theorem. -/
noncomputable def ofIsSemisimpleRing [IsSemisimpleRing R] :
    MatrixDivisionDecomposition.{uR, uR} R :=
  Classical.choice (nonempty_of_isSemisimpleRing R)

variable {R}

/-- The decomposition recovers any matrix tuple after applying its inverse. -/
@[simp]
theorem ringEquiv_apply_symm_apply (p : MatrixDivisionDecomposition.{uR, uD} R)
    (a : ∀ i, Matrix (Fin (p.blockSize i)) (Fin (p.blockSize i)) (p.coefficient i)) :
    p.ringEquiv (p.ringEquiv.symm a) = a :=
  p.ringEquiv.apply_symm_apply a

/-- The inverse decomposition recovers every original ring element. -/
@[simp]
theorem ringEquiv_symm_apply_apply (p : MatrixDivisionDecomposition.{uR, uD} R) (r : R) :
    p.ringEquiv.symm (p.ringEquiv r) = r :=
  p.ringEquiv.symm_apply_apply r

/-- Every block of a decomposition is nonempty, including when the outer
family itself is empty. -/
theorem blockSize_pos (p : MatrixDivisionDecomposition.{uR, uD} R) (i : Fin p.size) :
    0 < p.blockSize i :=
  Nat.pos_of_ne_zero (NeZero.ne (p.blockSize i))

end MatrixDivisionDecomposition
