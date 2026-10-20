public section

namespace TauCeti

open _root_.Matrix _root_.LieAlgebra.Orthogonal

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

theorem toEnd_typeDDiagonalCartan_matrix_eq_toLin_diagonal (A : typeDDiagonalCartan K ι) :
    LieModule.toEnd K (typeDDiagonalCartan K ι) (Matrix (ι ⊕ ι) (ι ⊕ ι) K) A =
      Matrix.toLin (Matrix.stdBasis K (ι ⊕ ι) (ι ⊕ ι))
        (Matrix.stdBasis K (ι ⊕ ι) (ι ⊕ ι))
        (Matrix.diagonal fun p : (ι ⊕ ι) × (ι ⊕ ι) => typeDMatrixWeight p.1 p.2 A) := by
  refine (Matrix.stdBasis K (ι ⊕ ι) (ι ⊕ ι)).ext fun p => ?_
  rw [LieModule.toEnd_apply_apply, Matrix.toLin_self,
    Finset.sum_eq_single p (fun q _ hq => by rw [Matrix.diagonal_apply_ne _ hq, zero_smul])
      (by simp),
    Matrix.diagonal_apply_eq, Matrix.stdBasis_eq_single]
  ext a b
  rw [typeDMatrixWeight_apply]
  simp only [LieSubalgebra.coe_bracket_of_module]
  have hA : (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈ diagonalCartan K (ι ⊕ ι) := by
    rw [mem_diagonalCartan_iff_isDiag]
    exact mem_typeDDiagonalCartan_iff_isDiag.mp A.2
  rw [lie_single_of_mem_diagonalCartan hA]

end TauCeti
end
