namespace P2MW.S_ModularCurve_nonempty_ssPlaces_fibre

attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

namespace SsfrobNE

open ModularCurve AlgebraicCurve

noncomputable section

open AlgebraicCurve IntermediateField Polynomial

namespace ModularCurve

section JLine

variable (K : Type) [Field K] (N : ℕ) [NeZero N]

theorem jLineEquivOneC_commutes (c : K) :
    (jLineEquivOneC K N).toRingEquiv (algebraMap K _ c) = algebraMap K _ c :=
  (jLineEquivOneC K N).commutes c

end JLine
end ModularCurve
end
end SsfrobNE
end P2MW.S_ModularCurve_nonempty_ssPlaces_fibre
