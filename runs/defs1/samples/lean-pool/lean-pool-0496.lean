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
  {S : Set Space} {hS : IsCompact S} {τ : ℝ}
  (P : ParentFrame (A.transverseData m hm R S hS) τ)

variable (hτ : 0 < τ) (hτT : τ < A.T)

/-- Activation frame, constructed using `P.reframe`. -/
def activationFrame : ParentFrame (P.activationData hτ hτT) τ :=
  P.reframe (P.activationNormal hτ hτT) (P.activationNormal_unit hτ hτT)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.activationNormal hτ hτT)))

end EulerPacketSourceGeometry.ParentFrame
end
end
end
end
