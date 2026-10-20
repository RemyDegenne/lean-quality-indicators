public section

noncomputable section

open CategoryTheory TensorProduct

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

section MatrixBasis

universe uK um un

theorem matrixStdBasis_dual_apply
    (K : Type uK) (m : Type um) (n : Type un)
    [CommSemiring K] [Fintype m] [Finite n] [DecidableEq (m × n)]
    (A : Matrix m n K) (i : m) (j : n) :
    (Matrix.stdBasis K m n).dualBasis (i, j) A = A i j := by
  rw [Module.Basis.dualBasis_apply]
  exact matrixStdBasis_repr K m n A i j

end MatrixBasis
end AlgebraicGeometry
end
end
