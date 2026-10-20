namespace P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0

open scoped MatrixGroups ModularForm

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

p2m_reactivate

namespace R4RRN

open UpperHalfPlane Complex Function

open scoped ModularForm Real Manifold Topology

variable {q : ℕ} [NeZero q] {M' : ℕ} [NeZero M']

section Slash

variable (hqM' : Nat.Coprime q M')

include hqM'

theorem FF_slash_eq {k : ℤ} (f : ModularForm (Γ q M') k) (γ : SL(2, ℤ)) :
    (⇑(FF hqM' f) : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) = ((⇑f : ℍ → ℂ) ∣[k] conjElemN q γ) ∣[k] (Dr q)⁻¹ := by
  rw [slash_conjElem_eq_FF, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

end Slash
end R4RRN
end
end P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0
