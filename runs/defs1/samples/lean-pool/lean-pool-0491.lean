@[expose] public section

noncomputable section

open Set Function Filter MeasureTheory

open scoped ContDiff Interval Topology BigOperators

namespace NavierStokes.FourierAlias

open TorusInverse

/-- State: an abbreviation for `ℝ × Plane`. -/
abbrev State := ℝ × Plane

end NavierStokes.FourierAlias
end
end
