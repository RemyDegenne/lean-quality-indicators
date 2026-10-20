@[expose] public section

noncomputable section

namespace EulerTransverseFixedEvolution

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerTimeLp
  EulerTerminalTimePrimitive EulerVolterraConvolution EulerTimeH1OperatorProduct
  EulerTimeH1FrameTransport EulerTransverseFixedSpaceInverse EulerTransverseGramInverse
  EulerContinuousTimeIntegral EulerTimeH1ContinuousDerivative

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖Q t v‖ ^ 2)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t v, ⟪H t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

theorem displacementPath_initial (f : TimeLp T E) :
    displacementPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall f ⟨0,le_rfl,hT⟩ = 0 :=
  velocityLp_zero_trace T hT Q Q₁ H c hc hQ hd K hK hH hsmall f

end EulerTransverseFixedEvolution
end
end
