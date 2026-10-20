namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isWeightedOrbitalIntegral_scalar_mul_diagUnits2

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions

set_option linter.unusedSectionVars false

namespace K56FIN

open AutomorphicForm

section sigma

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem normString_eq_P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = P K L A σ δ (Module.finrank K L) := rfl

end sigma
end K56FIN
end P2MW.S_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isWeightedOrbitalIntegral_scalar_mul_diagUnits2
