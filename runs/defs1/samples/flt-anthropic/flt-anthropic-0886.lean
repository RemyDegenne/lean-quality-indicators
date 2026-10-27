namespace P2MW.S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

universe u v

noncomputable section

open MvPowerSeries

namespace P2mKcCommutantLT

variable {p : ℕ} [Fact p.Prime]

section Main

variable {κ : Type u} [Field κ] [Fintype κ] [CharP κ p]

variable {k : Type v} [Field k] [CharP k p]

variable (j : WittVector p κ →+* k)

variable (G : MvFormalGroup 1 k) [G.IsComm]

variable (ρ : WittVector p κ →+* MvFormalGroup.End G)

local notation "𝕎" => WittVector p κ

local notation "q" => Fintype.card κ

variable (p κ) in

def ff : ℕ := ((FiniteField.card κ p).choose : ℕ+)

end Main
end P2mKcCommutantLT
end
end P2MW.S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card
