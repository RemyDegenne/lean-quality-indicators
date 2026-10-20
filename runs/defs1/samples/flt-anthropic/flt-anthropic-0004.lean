namespace P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open MeasureTheory MeasureTheory.Measure TopologicalSpace Function NumberField IsDedekindDomain

open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal

open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace P2mInertEvalGlue

open AutomorphicForm

section NormString

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

def unitNorm (u : (L ⊗[K] A)ˣ) : (L ⊗[K] A)ˣ :=
  ∏ i ∈ Finset.range (Module.finrank K L), (⇑(sigmaUnits K L A σ))^[i] u

end NormString
end P2mInertEvalGlue
end
end P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension
