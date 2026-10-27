@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerPacketNormalizedPrimary
  EulerPacketCrossProduct EulerTransversePacketProvider

/-- Activation direction, given by `unit (F.toContinuousLinearMap.adjoint n)`. -/
def activationDirection (F : Space ≃L[ℝ] Space) (n : Space) : Space :=
  unit (adjoint (𝕜 := ℝ) (E := Space) (F := Space) F.toContinuousLinearMap n)

end EulerPacketMovingFrame
end
end
