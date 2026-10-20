public section

open Bundle Function Manifold VectorField

open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

@[simp]
theorem mulInvariantCoordinateVectorField_add [IsManifold I 1 G] (v w y : E) :
    mulInvariantCoordinateVectorField (I := I) (G := G) (v + w, y) =
      mulInvariantCoordinateVectorField (I := I) (G := G) (v, y) +
        mulInvariantCoordinateVectorField (I := I) (G := G) (w, y) := by
  let g := (extChartAt I (1 : G)).symm y
  let A := tangentCoordChange I g (1 : G) g
  calc
    A (tangentVectorModelSpace (I := I) <|
        mulInvariantVectorField (I := I) (G := G)
          ((v + w : E) : GroupLieAlgebra I G) g) =
        A (tangentVectorModelSpace (I := I) <|
            mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) g) +
          A (tangentVectorModelSpace (I := I) <|
            mulInvariantVectorField (I := I) (G := G) (w : GroupLieAlgebra I G) g) := by
      rw [← map_add]
      apply congrArg A
      -- Compare the underlying tangent vectors before their definitional model-space conversion.
      change mulInvariantVectorField (I := I) (G := G)
          ((v + w : E) : GroupLieAlgebra I G) g =
        mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) g +
          mulInvariantVectorField (I := I) (G := G) (w : GroupLieAlgebra I G) g
      have hparameter : ((v + w : E) : GroupLieAlgebra I G) =
          (v : GroupLieAlgebra I G) + (w : GroupLieAlgebra I G) := rfl
      rw [hparameter]
      exact congrFun (mulInvariantVectorField_add (I := I) (G := G)
        (v : GroupLieAlgebra I G) (w : GroupLieAlgebra I G)) g

end
end
