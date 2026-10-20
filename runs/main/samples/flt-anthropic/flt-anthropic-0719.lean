namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_eq_of_forall_evalAt_eq_of_forall_iff_evalAt_eq_zero

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instTopologicallyFGOfFiniteType

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

open scoped IntermediateField

namespace R1AF8D2b

section Instance

variable {F : Type*} [Field F]

theorem flat_comp_completion (N : Subring F) [IsNoetherianRing N] [IsLocalRing N] {R : Type*} [CommRing R]
    (ι : AdicCompletion (maximalIdeal N) N ≃+* R) :
    (ι.toRingHom.comp (algebraMap N (AdicCompletion (maximalIdeal N) N))).Flat :=
  RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance) (RingHom.Flat.of_bijective ι.bijective)

end Instance
end R1AF8D2b
end
end P2MW.S_AlgebraicCurve_NodeAnnulusEngine_eq_of_forall_evalAt_eq_of_forall_iff_evalAt_eq_zero
