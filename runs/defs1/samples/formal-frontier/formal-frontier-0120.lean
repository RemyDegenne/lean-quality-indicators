public section

noncomputable section

open CategoryTheory TensorProduct

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

section End

variable (V : Type u) [AddCommGroup V] [Module K V]

variable [FiniteDimensional K V]

section Basis

variable (i : Type u) [Fintype i] [DecidableEq i] (b : Module.Basis i K V)

variable (j : Type u) [Fintype j] [DecidableEq j] (c : Module.Basis j K V)

/-- Coordinates associated with two bases differ by a natural change of basis;
the canonical End representation itself has no chosen basis. -/
def endMatrixBasisChangeIso :
    additiveMatrixFunctor K i i ≅ additiveMatrixFunctor K j j :=
  (endMatrixGroupIso K V i b).symm ≪≫ endMatrixGroupIso K V j c

end Basis
end End
end AlgebraicGeometry
end
end
