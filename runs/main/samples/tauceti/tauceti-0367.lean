public section

namespace Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

theorem fromBlocks_mem_typeD {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]
    (A B C : Matrix ι ι K) (hB : B.transpose = -B) (hC : C.transpose = -C) :
    fromBlocks A B C (-A.transpose) ∈ LieAlgebra.Orthogonal.typeD ι K := by
  rw [LieAlgebra.Orthogonal.typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  -- The membership lemmas leave `Matrix.IsSkewAdjoint`; its matrix-form definition reduces to
  -- this equation, and no public rewrite lemma names that final definitional reduction.
  change (Matrix.fromBlocks A B C (-A.transpose)).transpose *
      LieAlgebra.Orthogonal.JD ι K =
    LieAlgebra.Orthogonal.JD ι K *
      (-Matrix.fromBlocks A B C (-A.transpose))
  simp only [LieAlgebra.Orthogonal.JD, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_neg, Matrix.fromBlocks_multiply, Matrix.transpose_neg,
    Matrix.transpose_transpose, hB, hC, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, mul_one, neg_neg]

end Matrix
end
