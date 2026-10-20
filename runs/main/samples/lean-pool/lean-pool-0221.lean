@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

namespace EulerTransverseFixedSpaceInverse

open Set InnerProductSpace ContinuousLinearMap MeasureTheory
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution
  EulerTimeH1OperatorProduct EulerTimeH1FrameTransport EulerCoerciveProjection
  EulerTransverseVariationalInverse EulerTransverseCoordinateRegularity

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))

variable (c : ℝ) (hc : 0 < c) (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

theorem fixedFrameSolver_weak (f : TimeLp T E) (v : zeroTraceDerivatives (U := U) T hT) :
    let u := fixedFrameSolver T hT Q Q₁ H c hc hQ hd K hK hH hsmall f
    ⟪fixedFrameDerivative T hT Q Q₁ u, fixedFrameDerivative T hT Q Q₁ v⟫_ℝ -
      ⟪timeMultiplier T hT H (fixedFramePrimitive T hT Q Q₁ u),
        fixedFramePrimitive T hT Q Q₁ v⟫_ℝ = -⟪f, fixedFramePrimitive T hT Q Q₁ v⟫_ℝ := by
  dsimp only
  rw [← fixedFrameOperator_inner]
  simp only [fixedFrameSolver, ContinuousLinearMap.comp_apply, operator_inverse_apply, neg_apply,
    inner_neg_left, adjoint_inner_left]

end EulerTransverseFixedSpaceInverse
end
end
