@[expose] public section

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}

/-- Property of being a modification of a stochastic process that satisfies the Kolmogorov
condition (`IsKolmogorovProcess`). -/
def IsAEKolmogorovProcess (X : T → Ω → E) (P : Measure Ω) (p q : ℝ) (M : ℝ≥0) : Prop :=
  ∃ Y, IsKolmogorovProcess Y P p q M ∧ ∀ t, X t =ᵐ[P] Y t

end ProbabilityTheory
end
