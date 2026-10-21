namespace OAI

section

noncomputable section

open scoped BigOperators NNReal

open MeasureTheory ProbabilityTheory Set

namespace SK.Analytic

namespace TripleTimeBlocks

variable {α : ℝ → ℝ} {r s₁ s₂ q : ℝ} (B : TripleTimeBlocks α r s₁ s₂ q)

theorem coefficient_le (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hq : q∈Icc (0:ℝ) 1) (hs : s₁ < s₂) :
    tripleQuadraticCoefficient β (β^2*s₂) B.c (B.w (s₂-s₁)⁻¹) B.t ≤
      tripleCDFTrialCoefficient β α (s₂-s₁)⁻¹ r s₁ s₂ q := by
  rcases B.normalized_stats hs with ⟨hK,_,hC⟩
  unfold tripleQuadraticCoefficient
  rw [B.scalar_susceptibility β ha hm hq,B.scalar_root_hessian β ha hm,
    B.tail_area hm,hK,B.common_error β hs]
  unfold tripleCDFTrialCoefficient
  change _+β^2*weightedCrossPenalty (B.w (s₂-s₁)⁻¹) 0*tripleCDFResponse β α s₂ q+_ ≤ _
  have H := mul_le_mul_of_nonneg_left (crossPenalty_response_le (ha s₁).1
    (B.normalized_penalty hm hs) (tripleCDFResponse β α s₂ q)) (sq_nonneg β)
  linarith

end TripleTimeBlocks
end SK.Analytic
end
end
end OAI
