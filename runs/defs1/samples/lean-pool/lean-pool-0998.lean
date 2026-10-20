@[expose] public section

open Complex Real Filter Topology MeasureTheory

open scoped BigOperators ComplexConjugate

namespace Hadamard

/-- An entire function has finite order if there exist ρ₀, R₀ such that
    |f(z)| < exp(|z|^ρ₀) whenever |z| ≥ R₀ -/
def hasFiniteOrder (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∃ (ρ₀ R₀ : ℝ), ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ < Real.exp (‖z‖ ^ ρ₀)

end Hadamard
end
