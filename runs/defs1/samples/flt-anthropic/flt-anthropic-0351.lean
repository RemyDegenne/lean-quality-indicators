namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_three_of_dvd

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

p2m_reactivate

p2m_reactivate

section Rho

variable {k : Type} [Field k]
  (B K : IntermediateField k (LaurentSeries k)) (K₀ : IntermediateField k ↥K)
  (hBK : ∀ x : LaurentSeries k, x ∈ B → x ∈ K)
  (hK₀ : ∀ w : ↥K, w ∈ K₀ ↔ ∃ x : LaurentSeries k, x ∈ B ∧ ((w : ↥K) : LaurentSeries k) = x)

def rhoE : ↥B ≃ₐ[k] ↥K₀ := AlgEquiv.ofBijective _ (rho_bijective B K K₀ hBK hK₀)

end Rho
end W1ISO
end
end P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_three_of_dvd
