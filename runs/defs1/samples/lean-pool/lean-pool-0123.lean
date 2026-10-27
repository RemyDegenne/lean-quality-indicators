@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal ContDiff

namespace QuadraticCarleson

/-- The fixed positive half of the scale-zero dyadic amplitude. -/
noncomputable def positiveDyadicBase (t : ℝ) : ℂ :=
  if 0 < t then (dyadicPsi 0 t : ℂ) else 0

end QuadraticCarleson
end
