namespace P2MW.S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Set Function

open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions

noncomputable section

namespace KcSemiLocalSigmaLinGen

section Generic

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

local notation "n" => Module.finrank K L

def μ (k j i : Fin n) : K := (bK K L).repr (bK K L k * bK K L j) i

end Generic
end KcSemiLocalSigmaLinGen
end
end P2MW.S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul
