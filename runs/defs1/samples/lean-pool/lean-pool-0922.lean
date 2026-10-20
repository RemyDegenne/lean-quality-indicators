@[expose] public section

namespace QFT

open MeasureTheory Complex Real Filter

open scoped ENNReal NNReal Topology ComplexConjugate Real InnerProductSpace BigOperators

namespace RPProof

open MeasureTheory Complex Real

open scoped ComplexConjugate

variable (m : ℝ) [Fact (0 < m)]

/-- The `yIntegralFactor` declaration. -/
noncomputable def yIntegralFactor (f : TestFunctionℂ) (ω : ℝ) (k_sp : SpatialCoords) : ℂ :=
  ∫ y : SpaceTime, f y *
    Complex.exp (-(ω * y 0)) * Complex.exp (Complex.I * spatialDot k_sp (spatialPart y))

end RPProof
end QFT
end
