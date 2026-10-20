namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_place_forall_iff_mem_and_hasValue_of_height_one_of_natCast_notMem

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

section

p2m_open

p2m_open

noncomputable section

namespace P2mWs19HorizNq

local notation "Qbar" => AlgebraicClosure ℚ

local notation "LS" => LaurentSeries (AlgebraicClosure ℚ)

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q]
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]

def ιC : ↥(jIntegralClosure (N * q) A K) →+* ↥(modularFunctionFieldBar (N * q)) :=
  Subring.inclusion ((show jIntegralClosure (N * q) A K ≤ (fieldOver (N * q) K).toSubring from fun x hx => hx.1).trans
    (fieldOver_le_modularFunctionFieldBar (N * q) K))

end P2mWs19HorizNq
end
end
end P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_place_forall_iff_mem_and_hasValue_of_height_one_of_natCast_notMem
