namespace P2MW.S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function ModularCurve

open scoped Real Manifold MatrixGroups ModularForm Topology

namespace X1BoundedDenominators

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Δ" => ModularForm.discriminant

section Core

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem disc_smul (α : SL(2, ℤ)) (τ : ℍ) :
    Δ (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

end Core
end X1BoundedDenominators
end
end P2MW.S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
