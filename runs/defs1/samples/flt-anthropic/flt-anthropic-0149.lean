namespace P2MW.S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open Polynomial

namespace AXL

variable (p : ℕ) [hp : Fact p.Prime]

local notation "Ω" => PadicAlgCl p

local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

noncomputable def E (n : ℕ) : ℝ := ∑ i ∈ Finset.range (Nat.log p n), ((p : ℝ)⁻¹) ^ i

end AXL
end P2MW.S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le
