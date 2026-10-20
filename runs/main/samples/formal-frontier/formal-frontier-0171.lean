@[expose] public section

noncomputable section

open CategoryTheory TensorProduct

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

section MatrixSchemeBasisChange

variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (i j : Type u) [Fintype i] [Fintype j]
  [DecidableEq i] [DecidableEq j]
  (b : Module.Basis i K V) (c : Module.Basis j K V)

omit [FiniteDimensional K V] in
theorem endMatrixSchemeBasisChangeIso_coordinate_comp :
    vectorGroupCoordinateMap K (Module.End K V) (Matrix j j K)
        (endMatrixBaseLinearEquiv K V j c).toLinearMap =
      (vectorGroupCoordinateMap K (Module.End K V) (Matrix i i K)
        (endMatrixBaseLinearEquiv K V i b).toLinearMap).comp
          (vectorGroupCoordinateMap K (Matrix i i K) (Matrix j j K)
            (endMatrixSchemeBasisLinearMap K V i j b c)) := by
  apply SymmetricAlgebra.algHom_ext
  ext φ
  simp [vectorGroupCoordinateMap_ι, endMatrixSchemeBasisLinearMap,
    LinearMap.comp_apply]
  congr 1
  ext f
  simp [LinearMap.comp_apply]

end MatrixSchemeBasisChange
end AlgebraicGeometry
end
end
