@[expose] public section

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerCylinderAngleAverage EulerTimeLp EulerTimeLpBoundedMap
  EulerTransverseGramInverse

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

variable (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
  (hf : ∀ t, EulerCylinderAngleAverage.average (V := E) P (f t) = 0)

include hf in
theorem accelerationPath_mean_zero (t : Icc (0 : ℝ) T) :
    EulerCylinderAngleAverage.average (V := U) P (D.accelerationPath P f t) = 0 := by
  rw [← D.accelerationPath_average P f t,averagedPath_zero P f hf,D.accelerationPath_zero P t]

end EulerCylinderDirichlet.Coefficients
end
end
