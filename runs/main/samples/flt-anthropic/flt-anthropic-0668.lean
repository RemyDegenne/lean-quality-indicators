namespace P2MW.S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1

set_option autoImplicit false

namespace A2W1E

open CongruenceSubgroup HeckeEis

open scoped MatrixGroups Manifold ModularForm

section ES

variable (N : ℕ) (n : ℕ)

variable {N n}

theorem isEichlerIntegral_smul {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(BinaryForm ℂ n)}
    (hF : IsEichlerIntegral n f F) (c : ℂ) :
    IsEichlerIntegral n (c • f) (fun τ => c • F τ) := by
  intro d τ
  have h := (hF d τ).const_mul c
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul, Pi.smul_apply]
  convert h using 1
  · rfl
  · rfl
  ring

end ES
end A2W1E
end P2MW.S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1
