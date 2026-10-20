namespace P2MW.S_ModularCurve_LambdaNodeLocalized_lambdaEval_aeval_sixteenth_sub_swap_eq_zero

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 16000000

noncomputable section

open ModularCurve IntermediateField Polynomial

namespace LambdaFrickeSol

scoped instance instIsScalarTowerRat {L : Type*} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : IsScalarTower ℚ F L :=
  IsScalarTower.of_algebraMap_eq' (by apply RingHom.ext_rat)

scoped instance : NeZero (4 : ℕ) := ⟨by norm_num⟩

variable (q : ℕ) [hq : Fact q.Prime]

scoped instance : NeZero q := ⟨hq.out.ne_zero⟩

section Supp

variable {R : Type*} [CommRing R]

theorem coeff_pow_of_suppGE_zero {x : LaurentSeries R} (hx : SuppGE 0 x) :
    ∀ m : ℕ, (x ^ m).coeff 0 = (x.coeff 0) ^ m
  | 0 => by
      rw [pow_zero, pow_zero]
      have h : (HahnSeries.C (1 : R) : LaurentSeries R).coeff 0 = 1 := by
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]
      rwa [map_one] at h
  | m + 1 => by
      rw [pow_succ, pow_succ, ← coeff_pow_of_suppGE_zero hx m]
      have h := coeff_mul_of_suppGE (hx.pow0 m) hx
      rwa [add_zero] at h

end Supp
end LambdaFrickeSol
end
end P2MW.S_ModularCurve_LambdaNodeLocalized_lambdaEval_aeval_sixteenth_sub_swap_eq_zero
