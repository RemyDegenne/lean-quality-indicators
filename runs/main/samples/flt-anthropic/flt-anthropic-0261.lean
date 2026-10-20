namespace P2MW.S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy

set_option autoImplicit false

set_option maxHeartbeats 3200000

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

p2m_reactivate

set_option autoImplicit false

noncomputable section

open Module

namespace AlgebraicCurve

p2m_open

p2m_reactivate

section Bridge

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

variable {A : Type*} [CommRing A] [Algebra A E] [Algebra A F] [IsScalarTower A E F]

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow mk.injEq algebraMap_mem' toValuationSubring mk ramificationIndex ramificationIndex_pos restrict mem_restrict_iff ord_restrict deg_restrict_mul_inertiaDeg fiber mem_fiber adicValuation_eq_exp_neg_ord sum_ramificationIndex_mul_inertiaDeg" end Place

p2m_reactivate

section Headline

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]

theorem stichtenothGenusExists_of_isFractionRing [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasPoleDivisorPackage
    (hasPoleDivisorPackage_of_isFractionRing T hA)

end Headline
end Place
end Bridge
end AlgebraicCurve
end
end
end
end
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank
