@[expose] public section

open Complex MeasureTheory Set Filter Topology

open scoped Real Interval

noncomputable section

/-- Segment 1: right vertical from (1/2 + H·i) down to ρ+1. -/
def fdBoundarySeg1 : ℝ → ℂ := fun t =>
  1 / 2 + (heightCutoff - t * (heightCutoff - Real.sqrt 3 / 2)) * I

end
end
