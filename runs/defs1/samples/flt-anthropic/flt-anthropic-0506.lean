namespace P2MW.S_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul

attribute [-instance] RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm

open scoped Pointwise

noncomputable section

namespace R4RSUnfold

section Bruhat

open scoped OnePoint

variable {F : Type} [Field F]

def rep : OnePoint F → GL (Fin 2) F
  | ∞ => 1
  | (ξ : F) => gl2Weyl * unipotentGL2 ξ

end Bruhat
end R4RSUnfold
end
end P2MW.S_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
