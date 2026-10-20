@[expose] public section

noncomputable section

namespace EulerTransverseEndpointParameter

open Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeH1FrameTransport
  EulerTimeLpCoefficientMap EulerTransverseVariationalInverse EulerTransverseGramInverse
  EulerTransverseFixedSpaceInverse EulerTransverseParameterRegularity
  EulerTransverseEndpointEnergy EulerTransverseFixedEndpoint
  EulerCoerciveProjection EulerHilbertCoerciveParameter

open scoped ContDiff

variable {P U E V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : P → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  {n : ℕ∞ω}

variable (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (Q x)) (Q₁ x t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hPotential : ∀ x t v, ⟪H x t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

theorem contDiff_fixedEndpointDerivative
    (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) (hH : ContDiff ℝ n H)
    (L : P → V →L[ℝ] TimeLp T E) (hL : ContDiff ℝ n L) :
    ContDiff ℝ n (fun x => fixedEndpointDerivative T hT (Q x) (Q₁ x) (H x)
      c hc (hLower x) (hd x) K hK (hPotential x) hsmall (L x)) :=
  hL.sub ((contDiff_fixedFrameDerivative T hT Q Q₁ hQ hQ₁).clm_comp
    (contDiff_fixedEndpointCorrection T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall
      hQ hQ₁ hH L hL))

end EulerTransverseEndpointParameter
end
end
