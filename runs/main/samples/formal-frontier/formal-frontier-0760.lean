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

theorem sourceOrderedEndMatrixScheme_points (R : Type u) [CommRing R] [Algebra K R]
    (f : Module.End R (SourceOrderedTensor K V R)) :
    (sourceOrderedEndPointsIso K V).hom.app (CommAlgCat.of K R) (.ofAdd f) ≫
        (endMatrixSchemeIso K V i b).hom.hom.hom =
      (matrixGroupPointsIso K i i).hom.app (CommAlgCat.of K R)
        (.ofAdd (endMatrixLinearEquiv K V i b R
          (sourceOrderedEndEquiv K V R f))) := by
  exact endMatrixSchemeIso_points K V i b R (sourceOrderedEndEquiv K V R f)

end MatrixScheme
end AlgebraicGeometry
end
end
