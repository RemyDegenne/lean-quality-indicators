@[expose] public section

open Complex MeasureTheory Set Filter Topology

open scoped Real Interval

noncomputable section

/-- The q-expansion radius at height H: e^(-2πH). -/
def seg5QRadiusH (H : ℝ) : ℝ := Real.exp (-2 * Real.pi * H)

end
end
