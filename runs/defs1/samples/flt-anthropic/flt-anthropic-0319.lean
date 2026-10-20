namespace P2MW.S_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

noncomputable section

open Polynomial Filter CerednikDrinfeld.Omega

namespace IdAff

open scoped Classical

namespace DData

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

variable (d : DData K)

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

local notation "R" => Valued.v (DData.R₀ d)

def U (A : Set K) : Prop := ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z ∈ A, v ((d.r k).evalAt z) < v e

end DData
end IdAff
end
end P2MW.S_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero
