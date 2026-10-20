@[expose] public section

noncomputable section

namespace EulerTransverseForwardInverse

open Set InnerProductSpace ContinuousLinearMap EulerVolterraConvolution
  EulerTransverseGramInverse EulerTransverseGramPath EulerTransverseNormalResidual
  EulerContinuousTimeIntegral EulerLinearDuhamel

variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, V →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖Q t v‖ ^ 2)

variable (U : Evolution T hT (generator T Q Q₁ c hc hQ))

/-- The literal normal pressure coefficient in source equation (11). -/
def pressureCoefficient (M : Icc (0 : ℝ) T → E →L[ℝ] E) (m : Icc (0 : ℝ) T → E)
    (f : C(Icc (0 : ℝ) T, E)) (a₀ : V) (t : Icc (0 : ℝ) T) : ℝ :=
  (⟪m t,f t⟫_ℝ - 2*⟪m t,M t (velocity T hT Q Q₁ c hc hQ U f a₀ t)⟫_ℝ) / ‖m t‖^2

end EulerTransverseForwardInverse
end
end
