@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

open Set Function Filter MeasureTheory

open scoped BigOperators ContDiff Topology

namespace NavierStokes.TerminalCompensation

/-- One half of a squared-profile change, against a power weight. -/
noncomputable def weightedChange (P : Patch) (lam : ℝ) (c : Coeff) (w x : ℝ) : ℝ :=
  x ^ w * ((baseProfile lam x + correction P c x) ^ 2 - (baseProfile lam x) ^ 2) / 2

end NavierStokes.TerminalCompensation
end
end
