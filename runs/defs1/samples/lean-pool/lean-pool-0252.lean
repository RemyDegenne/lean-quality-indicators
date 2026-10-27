@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

open Set Filter MeasureTheory Function

open scoped Topology ContDiff BigOperators

namespace NavierStokes.ShapeTransition

/-- Scaled family, given by `F (R * p.1, p.2)`. -/
noncomputable def scaledFamily (R : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := F (R * p.1, p.2)

end NavierStokes.ShapeTransition
end
end
