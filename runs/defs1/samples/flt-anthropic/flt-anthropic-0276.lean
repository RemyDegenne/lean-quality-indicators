namespace P2MW.S_AlgebraicCurve_finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

p2m_open

p2m_reactivate

namespace AlgebraicCurve

p2m_open

namespace RationalFunctionField

p2m_open

open Polynomial

open scoped Polynomial

section RiemannRoch

variable {k : Type*} [Field k]

variable [IsAlgClosed k] [DecidableEq (RatFunc k)]

def riemannRochSpaceEquiv (E : Divisor k (RatFunc k)) :
    degreeLT k (E.degree + 1).toNat ≃ₗ[k] riemannRochSpace E :=
  LinearEquiv.ofBijective
    ((divDivisorFn E).restrict (p := degreeLT k (E.degree + 1).toNat) (q := riemannRochSpace E)
      (fun P hP => by
        rw [divDivisorFn_apply]
        exact div_divisorFn_mem_riemannRochSpace E hP))
    ⟨fun P Q h => Subtype.ext (divDivisorFn_injective E (congrArg Subtype.val h)),
      fun ⟨f, hf⟩ => by
        obtain ⟨P, hP, rfl⟩ := exists_eq_div_divisorFn_of_mem E hf
        exact ⟨⟨P, hP⟩, Subtype.ext (by simp [LinearMap.restrict_apply])⟩⟩

end RiemannRoch
end RationalFunctionField
end AlgebraicCurve
end AlgebraicCurve
end
end P2MW.S_AlgebraicCurve_finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc
