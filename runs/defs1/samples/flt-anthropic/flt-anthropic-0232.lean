namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd

set_option autoImplicit false

p2m_reactivate

p2m_open

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 3200000

set_option maxHeartbeats 12800000

noncomputable section

p2m_open

open scoped MatrixGroups

namespace W1ISO

abbrev en (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

end W1ISO
end
end P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd
