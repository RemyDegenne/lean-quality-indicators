@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerPacketProfileRecursion
  EulerPacketCylinderField EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerCylinderFieldReflection EulerTransverseBoundedFrame

namespace Forcing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

variable (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t, (-x, -θ)) = -raw (t, (x, θ)))
  (hinit : reflection (V := U) P (I.value : CylinderL2 P U) = -(I.value : CylinderL2 P U))

include hSym hF hM hraw hinit in
theorem velocityPath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection (V := Space) P (G.fullVelocityPath I t) = -G.fullVelocityPath I t :=
  EulerSourceCylinderParity.velocity_reflection_neg P D.support D.support_measurable hSym
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    (D.frame_even hF) (D.frameDerivative_even hF hM) G.path I.value (G.path_reflection_neg hraw)
        hinit t

end Forcing
end EulerTransversePacketProvider
end
end
