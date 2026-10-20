@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal NNReal InnerProductSpace

universe u_1 u_2

namespace Malliavin

section Dual

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

/-- The `L²` class of a continuous linear functional. -/
noncomputable def dualLp (L : StrongDual ℝ W) : Lp ℝ 2 μ :=
  (IsGaussian.memLp_dual μ L 2 (by simp)).toLp L

end Dual
end Malliavin
end
