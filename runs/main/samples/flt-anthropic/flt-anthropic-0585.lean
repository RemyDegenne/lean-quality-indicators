namespace P2MW.S_CerednikDrinfeld_Omega_natCard_dvd_of_isUnit_of_forall_apply_smul_eq_of_v_apply_eq_mul_zpow

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open scoped MatrixGroups

open CerednikDrinfeld.Omega

namespace TubeStab

section Assembly

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "ι" => algebraMap K₀ K

variable (ϖ : PseudoUniformizer K₀ K)

theorem moebiusK_injective {α β γ δ : K} (hdet : α * δ - β * γ ≠ 0) {y z : K} (hy : γ * y + δ ≠ 0)
    (hz : γ * z + δ ≠ 0) (h : (α * y + β) / (γ * y + δ) = (α * z + β) / (γ * z + δ)) : y = z := by
  rw [div_eq_div_iff hy hz] at h
  have : (α * δ - β * γ) * (y - z) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hdet)

end Assembly
end TubeStab
end P2MW.S_CerednikDrinfeld_Omega_natCard_dvd_of_isUnit_of_forall_apply_smul_eq_of_v_apply_eq_mul_zpow
