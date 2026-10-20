namespace P2MW.S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar

set_option maxHeartbeats 4000000

set_option synthInstance.maxHeartbeats 400000

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA

p2m_open

open scoped Polynomial

noncomputable section

namespace TwoCuspAux

local notation "𝕂" => AlgebraicClosure ℚ

variable (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local instance] algRatFunc

attribute [local instance] isScalarTower_ratFunc

attribute [local instance] finite_ratFunc

attribute [local instance] isSeparable_ratFunc

theorem e_zero (hw : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ)) :
    ((cuspZeroBar ℓ).ramificationIndex (RatFunc 𝕂) : ℤ) = ℓ := by
  have h := (cuspZeroBar ℓ).ord_restrict (F := RatFunc 𝕂) RatFunc.X
  rw [algebraMap_eq, φ_X, restrict_eq_of_isCusp ℓ _ (isCusp_cuspZeroBar ℓ hw), (e_infty ℓ).2] at h
  have hj : (cuspZeroBar ℓ).ord (jb ℓ) = -ℓ := ord_cuspZeroBar_coeffEmb_jq ℓ hw
  rw [hj] at h
  linarith

end TwoCuspAux
end
end P2MW.S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar
