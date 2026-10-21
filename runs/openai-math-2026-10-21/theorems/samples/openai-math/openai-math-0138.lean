namespace OAI

section

section

noncomputable section

namespace LogConcaveSampling.Quadrature

open MeasureTheory Set Polynomial

open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}

lemma derivative_weights_norm (u : I → ℝ) {ψ : ℝ} (hψ : 0<ψ) :
    (∑i,|derivativeWeight u i/ψ|)=(∑i,|derivativeWeight u i|)/ψ := by
  simp only [abs_div,abs_of_pos hψ,Finset.sum_div]

end LogConcaveSampling.Quadrature
end
end
end
end OAI
