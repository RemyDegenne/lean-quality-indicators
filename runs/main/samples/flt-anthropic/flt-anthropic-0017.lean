namespace P2MW.S_ModularCurve_xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd

attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical MatrixGroups

p2m_open

namespace XHTopResidueCollapsePow

section Groups

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (t : ℕ)

scoped instance : (Gam M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

scoped instance [NeZero t] : (Gam' M H t).FiniteIndex := by
  haveI : NeZero (M * t) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * t)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right M t)).trans (Gamma1_le_GammaH M H)

scoped instance [NeZero t] : (CohCarrier.GammaH M (Hpm M H) ⊓ Gamma0 t).FiniteIndex := by
  haveI : NeZero (M * t) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * t)) (le_inf ?_ ?_)
  · exact (Gamma1_le_of_dvd (dvd_mul_right M t)).trans (Gamma1_le_GammaH M _)
  · exact (Gamma1_le_of_dvd (dvd_mul_left t M)).trans (Gamma1_in_Gamma0 _)

omit [NeZero M] in

theorem Gam'_le_pm : Gam' M H t ≤ CohCarrier.GammaH M (Hpm M H) ⊓ Gamma0 (M * t) :=
  inf_le_inf_right _ (GammaH_mono le_sup_left)

end Groups
end XHTopResidueCollapsePow
end
end P2MW.S_ModularCurve_xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd
