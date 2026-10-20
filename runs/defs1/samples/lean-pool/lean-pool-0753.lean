@[expose] public section

noncomputable section

namespace NavierStokes.GaussianTailFlat

open Set Filter Function

open scoped ContDiff Topology BigOperators

/-- Profile, given by `profileBump`. -/
noncomputable def profile : ℝ → ℝ := profileBump

end NavierStokes.GaussianTailFlat
end
end
