@[expose] public section

noncomputable section

namespace EulerMeanOperatorTranslation

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerTimeLp EulerTerminalTimePrimitive EulerTimeLpBoundedMap
  EulerMeanTimeTranslation EulerVolterraConvolution EulerMeanVariationalInverse
  EulerTimeH1OperatorProduct

@[simp] theorem translatePath_apply (T : ℝ) (a : Space)
    (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (t : Icc (0 : ℝ) T) :
    translatePath T a F t = translateOperator a (F t) := rfl

end EulerMeanOperatorTranslation
end
end
