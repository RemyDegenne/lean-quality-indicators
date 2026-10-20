namespace P2MW.S_ModularCurve_XHDRLevel_algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

p2m_open

open scoped MatrixGroups

namespace WChartField

theorem coeffEmb_injective (L : Type*) [Field L] [Algebra ℚ L] : Function.Injective (coeffEmb L) := by
  intro x y h
  ext k
  have := congrArg (fun s : LaurentSeries L => s.coeff k) h
  simp only [coeffEmb_coeff] at this
  exact (algebraMap ℚ L).injective this

end WChartField
end P2MW.S_ModularCurve_XHDRLevel_algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic
