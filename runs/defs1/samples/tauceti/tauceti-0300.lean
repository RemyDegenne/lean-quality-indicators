public section

open MeasureTheory ProbabilityTheory Set Filter

open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Pointwise Topology

namespace TauCeti

variable {f : ℝ → ℝ} {μ : Measure ℝ≥0}

/-- A positive measure on `ℝ≥0` **represents `f` by its Laplace transform on `(0, ∞)`** if the
exponential kernel `p ↦ e^{-tp}` is integrable against it for every `t > 0` and the resulting
transform agrees with `f` there.

The measure is *not* required to be finite: that is the whole point of the open-half-line
statement, and the integrability clause is what takes over the role finiteness plays in
`TauCeti.RepresentsLaplace`. -/
def RepresentsLaplaceOnIoi (μ : Measure ℝ≥0) (f : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 < t → Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ) ∧
    ∀ t : ℝ, 0 < t → f t = laplaceTransform μ t

end TauCeti
end
