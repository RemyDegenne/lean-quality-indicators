namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

open scoped TensorProduct

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace BranchReadSkel

open ModularCurve AlgebraicCurve

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Maps

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) {hpM : p ∣ M}
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (R p) ↥A]

def wA : XA p M H hj A ⟶ XA p M H hj A :=
  pullback.map _ _ _ _ 𝔛.w.hom (𝟙 _) (𝟙 _) (by rw [𝔛.w_over, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

end Maps
end BranchReadSkel
end
end P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation
