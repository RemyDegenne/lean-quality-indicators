namespace P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker

open scoped MatrixGroups ModularForm

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

namespace R4RRN

variable (q : ℕ) [NeZero q] (M' : ℕ)

variable {q M'} {ℓg : ℕ} {H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ}

theorem mul_apply_10 (A B : SL(2, ℤ)) : (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

end R4RRN
end
end P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker
