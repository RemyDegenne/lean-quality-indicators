namespace P2MW.S_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash

set_option autoImplicit false

set_option maxHeartbeats 3200000

noncomputable section

namespace TraceDepletion

open CongruenceSubgroup ModularForm SlashInvariantForm Matrix MatrixGroups Function Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup

open _root_.Complex hiding Gamma

open UpperHalfPlane hiding I

open scoped Real ModularForm

local notation "𝕢" => Function.Periodic.qParam

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section FormE

variable {q t : ℕ} {k : ℤ}

theorem denom_SL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  rw [← ModularGroup.denom_apply]
  exact denom_ne_zero _ τ

end FormE
end TraceDepletion
end
end P2MW.S_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash
