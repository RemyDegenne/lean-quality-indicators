namespace P2MW.S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd

set_option autoImplicit false

set_option maxHeartbeats 3200000

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function

open scoped ModularForm MatrixGroups

noncomputable section

namespace ALDich

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Γ₀ℝ" M => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Reps

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

def traceRepMat : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => W.mat
  | some j => repMat q (some j)

end Reps
end ALDich
end
end P2MW.S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
