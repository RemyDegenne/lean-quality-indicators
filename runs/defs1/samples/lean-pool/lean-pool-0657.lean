section

@[expose] public section

noncomputable section

namespace NavierStokes.AxisSourceRegularity

open SimilarityProfile Set Filter

open scoped BigOperators Topology ContDiff

/-- Shifted axial factor as an element of `ℕ → InnerProfile | 0 => fun _ => 0 | k + 1 => Z2 h
(slowOrder h k - 1) (v k)`. -/
noncomputable def shiftedAxialFactor (h : ℝ) (v : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => Z2 h (slowOrder h k - 1) (v k)

end NavierStokes.AxisSourceRegularity
end
end
end
