namespace P2MW.S_ModularCurve_XZeroP_exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul

attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace B3CARRIER

section Coeff

variable {A : Type} [CommRing A] [IsDomain A] [ValuationRing A] {L : Type} [Field L] [Algebra A L]
  [IsFractionRing A L] [Algebra L (AlgebraicClosure ℚ)] [Algebra A (AlgebraicClosure ℚ)]
  [IsScalarTower A L (AlgebraicClosure ℚ)]
  {B : ValuationSubring (AlgebraicClosure ℚ)} {K : IntermediateField ℚ (AlgebraicClosure ℚ)}

abbrev HB (B : ValuationSubring (AlgebraicClosure ℚ)) : Prop := ∀ a : A, algebraMap A (AlgebraicClosure ℚ) a ∈ B

end Coeff
end B3CARRIER
end
end P2MW.S_ModularCurve_XZeroP_exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul
