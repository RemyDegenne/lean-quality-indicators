public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace TauCeti

/-- A measure `μ` and coefficients `a, b ≥ 0` represent a complete Bernstein function when
`μ` satisfies the standard Stieltjes integrability condition and the function agrees on
`[0, ∞)` with `a + b t + ∫ x, t / (t + x) ∂μ`.  Requiring `μ {0} = 0` stops an atom at zero from
making the integral term jump between zero and the positive parameters. -/
def RepresentsCompleteBernstein (μ : Measure ℝ≥0) (a b : ℝ≥0) (f : ℝ → ℝ) : Prop :=
  μ {0} = 0 ∧ Integrable stieltjesWeight μ ∧
    EqOn f (stieltjesBernsteinTransform μ a b) (Ici 0)

end TauCeti
end
end
