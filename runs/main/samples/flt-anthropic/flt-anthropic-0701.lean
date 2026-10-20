namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

p2m_open

open scoped MatrixGroups TensorProduct

noncomputable section

namespace WChart

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj)

local notation "𝕂" => AlgebraicClosure ℚ

scoped instance isIso_wBar : IsIso (wBar 𝔓) := by
  unfold wBar; infer_instance

@[reassoc] theorem wBar_fst : wBar 𝔓 ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔓.w.hom := by
  unfold wBar; exact pullback.lift_fst _ _ _

end WChart
end
end P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap
