@[expose] public section

open MeasureTheory Set Filter Asymptotics

open scoped Topology ENNReal

namespace QuadraticCarleson

/-- Positive homogeneity is stated pointwise, including infinite outputs. -/
def NonnegativeOperator.PositivelyHomogeneous (T : NonnegativeOperator) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (f : L0Infinity) (x : ℝ),
    T (scaleL0Infinity a f) x = ENNReal.ofReal a * T f x

end QuadraticCarleson
end
