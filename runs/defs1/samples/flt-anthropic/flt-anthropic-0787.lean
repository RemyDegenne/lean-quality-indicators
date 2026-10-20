namespace P2MW.S_AutomorphicForm_map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

open MeasureTheory Set AutomorphicForm Topology

open scoped TensorProduct TensorProduct.RightActions ENNReal

noncomputable section

namespace P2mGramBox

def ridE : Ecx ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
    (Algebra.TensorProduct.rid ℝ ℝ ℂ)

end P2mGramBox
end
end P2MW.S_AutomorphicForm_map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real
