namespace P2MW.S_ModularCurve_coe_diamondAutHBar_eq_qExpand_coe_diamondAutHBar_div_of_coe_eq_qExpand

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace DBetaBar

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ}

theorem one_mem_strictPeriods_bot : (1 : ℝ) ∈ (Γb M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

end Group
end DBetaBar
end
end P2MW.S_ModularCurve_coe_diamondAutHBar_eq_qExpand_coe_diamondAutHBar_div_of_coe_eq_qExpand
