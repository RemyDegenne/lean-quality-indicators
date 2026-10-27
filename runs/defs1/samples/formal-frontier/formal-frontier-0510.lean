@[expose] public section

noncomputable section

open CategoryTheory TensorProduct

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

section MatrixScheme

variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V]
  (i : Type u) [Fintype i] [DecidableEq i] (b : Module.Basis i K V)

variable [FiniteDimensional K V]

/-- The same comparison followed by the existing native matrix points. -/
def sourceOrderedEndMatrixPointsIso :
    sourceOrderedAdditiveEndFunctor K V ≅
      vectorGroupPointsFunctor K (Matrix i i K) :=
  sourceOrderedEndMatrixGroupIso K V i b ≪≫ matrixGroupPointsIso K i i

end MatrixScheme
end AlgebraicGeometry
end
end
