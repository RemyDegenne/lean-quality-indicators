@[expose] public section

noncomputable section

namespace EulerPacketForwardRadius

open EulerParameterWordGevrey EulerPacketRadiusPolynomial EulerPacketSourceRadius
  EulerPacketTerminalDatum EulerPacketCylinderField EulerPacketProfileRecursion
  EulerTransversePacketProvider

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (L : EulerTransversePacketForward.Budget D (Fin 4) 6)

variable {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R) (BC : CoefficientBudget C)
  (δ : ℝ) (ξ : U)

theorem canonicalRadius_power (W : ℝ) (hδ : 0 < δ)
    (H : RadiusPrimitives L LM N BC δ ξ W) :
    canonicalRadius L LM N BC δ ξ ≤ radiusConstant*W^radiusPower :=
  (canonicalRadius_le_envelope L LM N BC δ ξ W hδ H).trans (radiusEnvelope_power W H.one)

end EulerPacketForwardRadius
end
end
