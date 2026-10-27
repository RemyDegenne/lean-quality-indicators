public section

noncomputable section

open scoped BoundedContinuousFunction

open NormedSpace

namespace BoundedContinuousFunction

variable {α : Type*} [TopologicalSpace α]

/-- The exponential multiplier `x ↦ exp (-(t * m x))` as a bounded continuous function. -/
def expNegMul (m : α →ᵇ ℝ) (t : ℝ) : α →ᵇ ℝ :=
  exp (t • (-m))

end BoundedContinuousFunction
end
end
