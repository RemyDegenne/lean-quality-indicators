@[expose] public section

open MeasureTheory Real

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- A random variable `X` has a sub-Gaussian moment-generating function with parameter `c`
with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)` is `μ`-integrable and
the moment-generating function of `X` is bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
This implies in particular that `X` has expectation 0.

This is equivalent to `Kernel.HasSubgaussianMGF X c (Kernel.const Unit μ) (Measure.dirac ())`,
as proved in `HasSubgaussianMGF_iff_kernel`.
Properties about sub-Gaussian moment-generating functions should be proved first for
`Kernel.HasSubgaussianMGF` when possible. -/
structure HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, mgf X μ t ≤ exp (c * t ^ 2 / 2)

end ProbabilityTheory
end
