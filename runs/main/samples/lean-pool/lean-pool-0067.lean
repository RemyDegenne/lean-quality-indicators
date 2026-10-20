@[expose] public section

noncomputable section

namespace EulerPacketGeometrySourceGrowth

open Set InnerProductSpace EulerSmoothLimit EulerPacketMovingFrame
  EulerPacketMovingFrame.PhysicalGeometryData EulerPacketSourcePropagator
  EulerTransversePacketProvider

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U) {Ω : Set Space} (G : PhysicalGeometryData {x : Space // x ∈ Ω})
  {F F₁ Z Z₁ : ℝ → ℝ} (H : PhysicalGeometryConclusion G F F₁ Z Z₁)

theorem growthConstant_pos : 0 < growthConstant G := by
  unfold growthConstant
  positivity [G.Theta_pos,G.epsilon_pos]

end EulerPacketGeometrySourceGrowth
end
end
