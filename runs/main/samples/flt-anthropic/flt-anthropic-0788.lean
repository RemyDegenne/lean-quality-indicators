namespace P2MW.S_ModularCurve_FullLevel_not_mem_igusaNodes_of_reads_of_goodPt_twoChartIntegralModel_of_eq_two

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup

open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace L2Aux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

universe u

section PlaceNonunits

variable {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb)

theorem evalAt_eq_zero_iff_mem_nonunits (hP : P.IsRational) {f : Fb} (hf : f ∈ P.toValuationSubring) :
    P.evalAt f = 0 ↔ f ∈ P.toValuationSubring.nonunits := by
  constructor
  · intro h
    have := sub_algebraMap_evalAt_mem_nonunits P hP hf
    rwa [h, map_zero, sub_zero] at this
  · intro h
    exact evalAt_eq_of_sub_algebraMap_mem_nonunits P hP hf (c := 0) (by rwa [map_zero, sub_zero])

end PlaceNonunits
end L2Aux
end P2MW.S_ModularCurve_FullLevel_not_mem_igusaNodes_of_reads_of_goodPt_twoChartIntegralModel_of_eq_two
