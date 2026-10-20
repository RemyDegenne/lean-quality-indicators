@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTimeIntervalRestriction
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit
  EulerPacketProfileRecursion EulerCylinderAngleAverage

open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField}

namespace HistoryData

variable (B : HistoryData D) (G : Forcing P D raw)

/-- The history trace in the same fixed reference-plane coordinates is the
actual initial datum passed to the forward interval. -/
def forwardInitial (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T) :
    InitialData P (D.tail τ hτ.le hτT) where
  value := ((B.initial τ hτ hτT.le).terminalInitial (G.initial τ hτ hτT.le)).value
  orbit := ((B.initial τ hτ hτT.le).terminalInitial (G.initial τ hτ hτT.le)).orbit
  mean_zero := ((B.initial τ hτ hτT.le).terminalInitial (G.initial τ hτ hτT.le)).mean_zero

end HistoryData
end EulerTransversePacketProvider
end
end
