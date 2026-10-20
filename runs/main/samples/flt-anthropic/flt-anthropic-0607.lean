namespace P2MW.S_AlgebraicCurve_finrank_twistedNodeCompatible_add_min_card_le_of_ringEquiv_ratFunc

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace AlgebraicCurve

p2m_open

namespace RationalFunctionField

p2m_open

open Polynomial

open scoped Polynomial

p2m_reactivate

section Nodes

variable {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] [DecidableEq (RatFunc k)]

variable {ι : Type*}

theorem finiteDimensional_twistedPairs (E₁ E₂ : Divisor k (RatFunc k)) (a b : ι → k) (lam : ι → k) :
    FiniteDimensional k
      (twistedPairs E₁ E₂ (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i))
        (fun i => twistFn E₁ (a i)) (fun i => twistFn E₂ (b i)) lam) := by
  rw [twistedPairs_eq_map E₁ E₂ a b lam]
  infer_instance

end Nodes
end RationalFunctionField
end AlgebraicCurve
end AlgebraicCurve
end
end P2MW.S_AlgebraicCurve_finrank_twistedNodeCompatible_add_min_card_le_of_ringEquiv_ratFunc
