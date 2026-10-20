namespace P2MW.S_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles

set_option autoImplicit false

namespace A2BES

open UpperHalfPlane MvPolynomial CongruenceSubgroup HeckeEis Filter

open scoped MatrixGroups ModularForm Manifold Topology

section Analytic

variable {N : ℕ} {k : ℤ}

def mulN (N : ℕ) [NeZero N] (τ : ℍ) : ℍ :=
  ⟨(N : ℂ) * τ, by
    rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))) τ.im_pos⟩

end Analytic
end A2BES
end P2MW.S_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles
