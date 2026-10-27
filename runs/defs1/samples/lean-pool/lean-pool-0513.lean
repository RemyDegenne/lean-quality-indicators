@[expose] public section

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

/-- The second segment of the boundary polygon (chord from `ρ'` to `i`). -/
noncomputable def fdPolygonSeg2 : ℝ → ℂ := fun t =>
  chordSegment rho' iPoint (t - 1)

end RectHomotopyProof
end
