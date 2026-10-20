public section

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℤ) [(W.baseChange ℚ).IsElliptic]

theorem mem_integralPoints_iff (P : (W.baseChange ℚ).toAffine.Point) :
    P ∈ W.integralPoints ↔
      ∃ x y : ℤ, ∃ h : W.toAffine.Equation x y, P = W.pointOfIntegralSolution x y h :=
  Iff.rfl

end WeierstrassCurve
end
