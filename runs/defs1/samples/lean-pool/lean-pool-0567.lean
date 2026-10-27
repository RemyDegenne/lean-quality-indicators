@[expose] public section

noncomputable section

namespace EulerPacketParentLabelBounds

open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerMeanClassicalWordBounds EulerParameterWordGevrey
  EulerGevrey EulerOperatorGevreyCalculus

open scoped ContDiff

/-- Gradient amplitude, given by `embeddingCost*K^2`. -/
def gradientAmplitude (K : ℝ) : ℝ := embeddingCost*K^2

end EulerPacketParentLabelBounds
end
end
