namespace P2MW.S_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase

attribute [-instance] AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option autoImplicit false

set_option maxHeartbeats 3200000

open Polynomial

namespace AlgebraicCurve

p2m_open

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open Module IsDedekindDomain WithZero

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve

p2m_open

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem gate_indexOfSpecialty_engine_at_witness [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    (indexOfSpecialty D₀ : ℤ) = 0 := by
  exact_mod_cast indexOfSpecialty_eq_zero_of_genusReached h

end AlgebraicCurve
end
end
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
