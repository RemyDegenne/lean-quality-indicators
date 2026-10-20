public section

open Bundle Function Manifold VectorField

open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- The left-invariant vector field, expressed in the identity chart and parameterized by its
generating tangent vector in the model space. -/
noncomputable def mulInvariantCoordinateVectorField [IsManifold I 1 G] (p : E × E) : E :=
  let g := (extChartAt I (1 : G)).symm p.2
  tangentCoordChange I g (1 : G) g
    (mulInvariantVectorField (I := I) (G := G) p.1 g)

end
end
