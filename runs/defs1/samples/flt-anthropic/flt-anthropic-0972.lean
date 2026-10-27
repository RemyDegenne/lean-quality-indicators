namespace P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Slot

open Finset

noncomputable def DS.transport {n J : ℕ} (σ : ℝ) (e : Fin n → ℂ) (c : Fin n → Fin J → ℂ)
    (i : Fin n) (m : Fin J) : ℂ :=
  ∑ j : Fin J, (if (m : ℕ) ≤ (j : ℕ) then (((j : ℕ).choose m : ℕ) : ℂ) * ((Real.log σ : ℝ) : ℂ) ^ ((j : ℕ) - m)
    else 0) * ((((σ : ℝ) : ℂ) ^ e i) * c i j)

end Slot
end P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top
