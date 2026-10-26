/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.ElementaryDiagonal
public import GeneralLinearGroups.RectangularUpperAction

/-!
# Diagonalization from elementary unit pivots

A unit pivot produced by an elementary left factor for every invertible matrix
at every successor rank reduces the diagonalization problem to the invertible
Schur residual. The premise is a property of the coefficient ring, not an
unconditional existence result for elementary pivot factors.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [CommRing R]

/-- If elementary left factors produce unit leading entries at every successor
rank, every invertible finite matrix admits a two-sided elementary reduction
to a diagonal of units, including in rank zero. -/
theorem exists_elementary_diagonalization_of_unit_pivots
    (pivot : ∀ (rank : ℕ) (matrix : GL (Fin (rank + 1)) R),
      ∃ factor : elementarySubgroup (Fin (rank + 1)) R,
        IsUnit (((((factor : GL (Fin (rank + 1)) R) * matrix) :
          GL (Fin (rank + 1)) R) : Matrix (Fin (rank + 1)) (Fin (rank + 1)) R) 0 0))
    {rank : ℕ} (matrix : GL (Fin rank) R) :
    ∃ (left right : elementarySubgroup (Fin rank) R) (diagonal : Fin rank → Rˣ),
      (left : GL (Fin rank) R) * matrix * (right : GL (Fin rank) R) =
        diagonalUnit diagonal := by
  induction rank with
  | zero =>
      refine ⟨1, 1, (fun index => index.elim0), ?_⟩
      apply Units.ext
      ext index
      exact index.elim0
  | succ rank ih =>
      obtain ⟨factor, hpivot⟩ := pivot rank matrix
      let corrected : GL (Fin (rank + 1)) R :=
        (factor : GL (Fin (rank + 1)) R) * matrix
      let M : Matrix (Fin (rank + 1)) (Fin (rank + 1)) R := corrected
      let T := Matrix.firstRestBlock M
      let A := T.toBlocks₁₁
      let B := T.toBlocks₁₂
      let C := T.toBlocks₂₁
      let D := T.toBlocks₂₂
      have hA : IsUnit A.det := by
        change IsUnit (Matrix.firstRestBlock M).toBlocks₁₁.det
        rw [Matrix.firstRestBlock_pivot]
        simpa [Matrix.leadingPrincipalMinor, Matrix.det_fin_one, M, corrected] using hpivot
      let inverseA : Invertible A := Matrix.invertibleOfIsUnitDet A hA
      let S := D - C * A⁻¹ * B
      have hM : IsUnit M := Units.isUnit corrected
      have hT : IsUnit T := by
        apply (Matrix.isUnit_iff_isUnit_det T).mpr
        have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
        simpa only [T, Matrix.firstRestBlock, Matrix.det_submatrix_equiv_self] using hMdet
      have hS : IsUnit S := by
        have hblock : IsUnit (Matrix.fromBlocks A B C D) := by
          simpa only [A, B, C, D, Matrix.fromBlocks_toBlocks] using hT
        simpa only [S, Matrix.invOf_eq_nonsing_inv] using
          (Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mp hblock)
      let residual : GL (Fin rank) R := hS.unit
      obtain ⟨left, right, diagonal, hdiagonal⟩ := ih residual
      have hSdiagonal :
          ((left : GL (Fin rank) R) : Matrix (Fin rank) (Fin rank) R) * S *
            ((right : GL (Fin rank) R) : Matrix (Fin rank) (Fin rank) R) =
              Matrix.diagonal (fun index => (diagonal index : R)) := by
        simpa only [Units.val_mul, diagonalUnit_val, residual, hS.unit_spec] using congrArg
          (fun unit : GL (Fin rank) R =>
            (unit : Matrix (Fin rank) (Fin rank) R)) hdiagonal
      obtain ⟨L, Q, entries, hfactor⟩ :=
        Matrix.exists_elementary_diagonalization_of_unit_pivot
          M hA left right diagonal hSdiagonal
      refine ⟨L * factor, Q, entries, ?_⟩
      apply Units.ext
      simpa only [Subgroup.coe_mul, Units.val_mul, corrected, M,
        Matrix.mul_assoc, diagonalUnit_val] using hfactor

end Matrix.GeneralLinearGroup
