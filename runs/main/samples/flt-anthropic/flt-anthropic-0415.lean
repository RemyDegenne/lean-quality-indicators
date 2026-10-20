namespace P2MW.S_ModularCurve_laurentBaseChange_x1FunctionField_sup_adjoin_qExpand_x1x0FunctionFieldC

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open scoped MatrixGroups

namespace X1LDLaurent

p2m_open

open scoped MatrixGroups

variable (K : Type*) [Field K]

variable {K}

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem coeffEmb_apply (x : LaurentSeries ℚ) : coeffEmb L x = x.map (algebraMap ℚ L) := rfl

end X1LDLaurent
end
end P2MW.S_ModularCurve_laurentBaseChange_x1FunctionField_sup_adjoin_qExpand_x1x0FunctionFieldC
