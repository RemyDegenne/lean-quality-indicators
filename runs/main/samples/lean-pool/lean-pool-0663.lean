@[expose] public section

noncomputable section

open scoped ContDiff

namespace EulerTimeLpGramInverse

open Set MeasureTheory InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerVolterraConvolution EulerTransverseGramInverse
  EulerTransverseGramPath EulerCoerciveProjection EulerTimeLpCoefficientMap
  EulerTimeLpCoefficientGevrey EulerOperatorGevreyCalculus EulerGevrey

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gramOperator_ae (T : ℝ) (hT : 0 ≤ T)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (u : TimeLp T U) :
    ∀ᵐ t ∂timeMeasure T, gramOperator T hT Q u t =
      adjoint (𝕜 := ℝ) (E := U) (F := E) (Q (projIcc 0 T hT t))
        (Q (projIcc 0 T hT t) (u t)) := by
  simp only [gramOperator, comp_apply, timeMultiplier_adjoint]
  filter_upwards [timeMultiplier_ae T hT (adjointPath T Q) (timeMultiplier T hT Q u),
    timeMultiplier_ae T hT Q u] with t hA hQ
  rw [hA, hQ]
  rfl

end EulerTimeLpGramInverse
end
end
