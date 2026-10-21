namespace OAI

noncomputable section

open scoped BigOperators

open MeasureTheory ProbabilityTheory Filter

open scoped Topology NNReal

open scoped BigOperators

open MeasureTheory ProbabilityTheory Polynomial Filter

open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory WithLp

open scoped BigOperators RealInnerProductSpace

namespace MinUncut.GaussianHermite

open MeasureTheory ProbabilityTheory

open scoped BigOperators

lemma integral_expect {T Ω : Type*} [Fintype T] [MeasurableSpace Ω] {μ : Measure Ω}
    (f : T → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) :
    (∫ x, (𝔼 t, f t x) ∂μ) = 𝔼 t, ∫ x, f t x ∂μ := by
  simp only [Finset.expect_eq_sum_div_card]
  rw [integral_div, integral_finsetSum _ (fun t _ => hf t)]

end MinUncut.GaussianHermite
end
end OAI
