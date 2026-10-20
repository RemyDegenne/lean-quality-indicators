@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal NNReal InnerProductSpace

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

noncomputable
section

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem norm_sub_expectationL2_le_mderivD12
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ‖F.1 - expectationL2 F.1‖ ≤ ‖mderivD12 P F‖ := by
  rw [norm_sub_expectationL2 C F]
  exact norm_predictableDerivative_le C F

end Malliavin
end
end
