@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace QuadraticCarleson

namespace PositiveGoodOscillatory

open OscillatoryReduction PositiveHighHeightEstimate

/-- The oscillatory maximal function with modulation restricted to integer powers of two. -/
noncomputable def paperLacunaryOscillatoryMaximal (b : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ m : ℤ, ‖paperOscillatoryAction (dyadicModulation m) (dyadicModulation_pos m).ne' b x‖ₑ

end PositiveGoodOscillatory
end QuadraticCarleson
end
