section

section

@[expose] public section

noncomputable section

namespace EulerPacketSourceGeometry.ParentFrame

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerTransversePacketProvider EulerTransverseFrameCoordinates
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketCrossProduct

variable {A : Parent} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {m : Space} {hm : ‖m‖ = 1} {R : U ≃ₗᵢ[ℝ] referencePlane m}
  {S : Set Space} {hS : IsCompact S}
  (P : ParentFrame (A.transverseData m hm R S hS) 0)

theorem forward_normal_choice : P.forwardData.m₀ =
    cross (unit (P.forwardFrame.m 0)) (unit (P.forwardFrame.v 0)) := rfl

end EulerPacketSourceGeometry.ParentFrame
end
end
end
end
