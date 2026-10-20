@[expose] public section

open MeasureTheory Filter Set Asymptotics

open scoped SchwartzMap Topology ENNReal

namespace QuadraticCarleson

/-- The set where a nonnegative Schwartz operator exceeds the given real level. -/
def schwartzOperatorLevelSet (T : SchwartzNonnegativeOperator) (f : 𝓢(ℝ, ℂ))
    (α : ℝ) : Set ℝ := {x | ENNReal.ofReal α ≤ T f x}

end QuadraticCarleson
end
