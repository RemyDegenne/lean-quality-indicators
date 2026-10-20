@[expose] public section

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal Real Topology

noncomputable
section

universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_8

namespace Malliavin.CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

theorem translated_eq_withDensity_zero :
    translated μ (0 : Space μ) = μ.withDensity (density μ (0 : Space μ)) := by
  rw [translated_zero, funext (density_zero μ)]
  exact withDensity_one.symm

end Malliavin.CameronMartin
end
end
