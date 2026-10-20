@[expose] public section

noncomputable section

namespace EulerInitialTimePrimitive

open MeasureTheory Set ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeH1FieldProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

variable (T : ℝ) (hT : 0 ≤ T) (A A₁ : C(Icc (0 : ℝ) T, E →L[ℝ] F))

variable (hd : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT A) (A₁ t) (Icc (0 : ℝ) T) t)

theorem initialPrimitive_constantFieldOperator (x : E) (t : Icc (0 : ℝ) T) :
    initialPrimitive T hT (constantFieldOperator T hT x) t = (t : ℝ) • x := by
  have hlin : AbsolutelyContinuousOnInterval (fun s : ℝ => s • x) 0 T :=
    (toSpanSingleton ℝ x).lipschitzWith.lipschitzOnWith.absolutelyContinuousOnInterval
  apply Eq.symm
  apply eq_initialRealPrimitive_of_ac_hasDerivAt_ae T hT (constantFieldOperator T hT x)
    (fun s : ℝ => s • x) hlin _ (zero_smul ℝ x) t t.property
  filter_upwards [constantFieldOperator_ae T hT x] with s hs
  rw [hs]
  simpa only [id_eq, one_smul] using (hasDerivAt_id s).smul_const x

end EulerInitialTimePrimitive
end
end
