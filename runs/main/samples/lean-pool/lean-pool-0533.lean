section

@[expose] public section

noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit EulerCylinderLocalSupport
  EulerCylinderAngleAverage EulerCylinderCorrectorMeanZero EulerPacketProfileRecursion
  EulerTransversePacketProvider EulerElapsedTimePathGluing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

theorem potentialTimePath_supported (t : Icc (0 : ℝ) D.T) :
    potentialTimePath τ hτ hτT B G t ∈ Supported P Space D.support D.support_measurable := by
  apply (Supported P Space D.support D.support_measurable).add_mem
  · exact EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
      (velocityPath τ hτ hτT B G) D.potentialDerivative (velocityPath_supported τ hτ hτT B G) t
  · exact EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
      (derivativePath τ hτ hτT B G) D.potentialCoefficientPath (derivativePath_supported τ hτ hτT B
          G) t

end EulerTransversePacketJoin
end
end
end
