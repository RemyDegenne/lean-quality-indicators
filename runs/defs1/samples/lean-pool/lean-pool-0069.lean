@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Function

open scoped ENNReal NNReal InnerProductSpace

universe u_1 u_2 u_3 u_4 u_5

noncomputable
section

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

local instance gaussianSFinite : SFinite P :=
  @probability_sFinite W _ P (IsGaussian.toIsProbabilityMeasure P)

/-- The algebraic span of all one-step adapted predictable processes. -/
def elementaryPredictableSpan [SFinite P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    Submodule ℝ (PredictableProcessL2 𝓕 P) :=
  Submodule.span ℝ {U | ∃ a b : ℝ≥0,
    ∃ _hab : a ≤ b, ∃ Z : lpMeas ℝ ℝ (𝓕 a) 2 P,
      U = elementaryPredictable 𝓕 a b Z}

end Malliavin
end
end
