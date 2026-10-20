@[expose] public section

open Function MeasureTheory Metric Set

open scoped ContDiff

namespace QuadraticCarleson

/-- The fixed normalized bump `φ` from the beginning of Section 3. -/
noncomputable def baseBump : ℝ → ℝ :=
  baseBumpData.normed volume

end QuadraticCarleson
end
