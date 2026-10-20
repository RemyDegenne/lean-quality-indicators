namespace P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle

set_option autoImplicit false

noncomputable section

namespace TT2

open UniformSpace Filter Topology

open scoped Pointwise NNReal

variable {p : ℕ} [Fact p.Prime]

local notation "Ω" => PadicAlgCl p

local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

p2m_reactivate

p2m_reactivate

p2m_reactivate

section values

variable (p)

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

omit [FiniteDimensional ℚ_[p] K] in
lemma mem_fixingSubgroup_F_of_mem_Kinf {τ : Γ} (hτ : τ ∈ (Kinf p K).fixingSubgroup) (n : ℕ) :
    τ ∈ (F p n).fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone ((F_le_Finf p n).trans le_sup_right) hτ

end values
end TT2
end
end P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle
