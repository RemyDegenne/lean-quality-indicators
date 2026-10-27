public section

noncomputable section

open CategoryTheory TensorProduct

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

section Matrix

variable (m n : Type u) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The additive rectangular matrix functor is represented by the affine
vector-group scheme. This extends the positive-size matrix example in Milne,
*Algebraic Groups* (2017), item 2.7, to empty finite index types. -/
@[expose] def matrixGroupPointsIso :
    additiveMatrixFunctor K m n ≅ vectorGroupPointsFunctor K (Matrix m n K) :=
  (matrixVectorGroupIso K m n).symm ≪≫ vectorGroupPointsIso K (Matrix m n K)

end Matrix
end AlgebraicGeometry
end
end
