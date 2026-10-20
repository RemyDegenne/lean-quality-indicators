@[expose] public section

open Complex MeasureTheory Real Finset

open scoped BigOperators ComplexConjugate Topology

noncomputable section

namespace HermiteLEAN

/-- The circle period used throughout the Hermite development. -/
def T : ℝ := 2 * Real.pi

end HermiteLEAN
end
end
