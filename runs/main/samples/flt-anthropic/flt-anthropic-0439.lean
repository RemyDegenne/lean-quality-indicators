namespace P2MW.S_AlgebraicCurve_finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached

attribute [-instance] AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

open Polynomial IsLocalRing

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

set_option autoImplicit false

noncomputable section

open Module IsDedekindDomain WithZero

p2m_reactivate

set_option autoImplicit false

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve

p2m_open

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

p2m_reactivate

variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]

namespace IntegralBasisInLSpace p2m_export "AlgebraicCurve.IntegralBasisInLSpace" "hu_indep c u mk.injEq hu_mem mk" end IntegralBasisInLSpace

p2m_open_scoped "AlgebraicCurve.IntegralBasisInLSpace" in

p2m_open_scoped "AlgebraicCurve.PoleDivisorPackage" in

theorem gate_stichtenothGenus_le_of_transcendenceTower [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T)
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    γ ≤ (Module.finrank E F : ℤ) * (IB.c - 1) + 1 :=
  gate_stichtenothGenus_le_of_poleDivisorPackage
    (PoleDivisorPackage.ofTranscendenceTower T IB) h

end IntegralBasisInLSpace
end AlgebraicCurve
end
end
end
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached
