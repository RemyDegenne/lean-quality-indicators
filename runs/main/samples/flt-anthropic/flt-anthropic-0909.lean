namespace P2MW.S_MeasureTheory_exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology

open scoped Real BigOperators ENNReal

noncomputable section

namespace WindB

section Package

variable {a b r : ℕ}

lemma dotR_sub_right (ξ x x' : Fin r → ℝ) : dotR ξ (x - x') = dotR ξ x - dotR ξ x' := by
  simp only [dotR, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

end Package
end WindB
end
end P2MW.S_MeasureTheory_exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay
