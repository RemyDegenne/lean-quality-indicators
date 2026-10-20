namespace P2MW.S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd

set_option autoImplicit false

set_option maxHeartbeats 3200000

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function

open scoped ModularForm MatrixGroups

noncomputable section

namespace ALDich

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Γ₀ℝ" M => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Square

variable {M q : ℕ} {k : ℤ} (W : AtkinLehnerDatum M q)

theorem alSlash_alSlash [NeZero M] (ε' : DirichletCharacter ℂ W.R) {F : ℍ → ℂ}
    (hF : IsOfType M k ε' F) :
    alSlash W k (alSlash W k F) = (ε' (q : ZMod W.R) * (q : ℂ) ^ (k - 2)) • F := by
  have hFu : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL) = ε' (q : ZMod W.R) • F := by
    rw [hF _ W.sqUnitSL_mem]
    congr 2
    show (((W.sqUnit 1 1 : ℤ)) : ZMod W.R) = _
    have : W.sqUnit 1 1 = (W.R : ℤ) * W.b + (q : ℤ) := by rw [AtkinLehnerDatum.sqUnit]; simp
    rw [this]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add]
  calc alSlash W k (alSlash W k F)
      = F ∣[k] (W.alGL * W.alGL) := by
        rw [alSlash_def, alSlash_def, SlashAction.slash_mul]
    _ = (F ∣[k] scalarGL q W.q_pos) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL) := by
        rw [alGL_mul_alGL, SlashAction.slash_mul]
    _ = ((q : ℂ) ^ (k - 2)) • (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL)) := by
        rw [slash_scalarGL, smul_slash_pos k (by simp)]
    _ = (ε' (q : ZMod W.R) * (q : ℂ) ^ (k - 2)) • F := by rw [hFu, smul_smul, mul_comm]

end Square
end ALDich
end
end P2MW.S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
