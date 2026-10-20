namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_twistSp_eq_zero_of_annulus

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

p2m_open

open scoped MatrixGroups

namespace CsHEqv

theorem restrictAlong_semilinearAut_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : SemilinearAut.IntertwinesAlong φ.toRingHom g g') (w : Place K F') :
    (g' • w).restrictAlong φ hφ = g • (w.restrictAlong φ hφ) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact SemilinearAut.restrict_smul (F := F) (g := g) (g' := g') (fun x => hgg' x) w

end CsHEqv
end P2MW.S_ModularCurve_JHPlaceSpecialization_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_twistSp_eq_zero_of_annulus
