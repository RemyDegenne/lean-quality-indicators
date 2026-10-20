@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal NNReal Real Topology InnerProductSpace

/-- The Malliavin derivative as the Riesz representative of differentiation
along the Cameron–Martin covariance embedding. -/
noncomputable def mderiv
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] (F : W → ℝ) (x : W) : CameronMartin.Space μ :=
  (InnerProductSpace.toDual ℝ (CameronMartin.Space μ)).symm
    ((fderiv ℝ F x).comp (CameronMartin.inclusion μ))

end
