namespace P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries

attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

p2m_open

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace CU2i

section ValCalc

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def evalHom (v : Place K F) (hv : v.IsRational) : v.toValuationSubring →+* K :=
  ((residueEquiv v hv).symm : v.ResidueField →+* K).comp (IsLocalRing.residue v.toValuationSubring)

end ValCalc
end CU2i
end
end P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries
