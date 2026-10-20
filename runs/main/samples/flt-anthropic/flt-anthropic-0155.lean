namespace P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero

set_option autoImplicit false

namespace HeckeEis

p2m_open

open MvPolynomial CongruenceSubgroup

open scoped MatrixGroups

namespace TorsionFreeAux

theorem aux_cancel {M : Type*} [AddCommGroup M] (f : M →+ M) (m : ℤ) (hinj : ∀ x : M, m • x = 0 → x = 0)
    (v' z : M) (h : f (m • v') - m • v' = m • z) : f v' - v' = z := by
  rw [map_zsmul, ← zsmul_sub] at h
  have h0 : m • (f v' - v' - z) = 0 := by rw [zsmul_sub, h, sub_self]
  exact sub_eq_zero.mp (hinj _ h0)

end TorsionFreeAux
end HeckeEis
end P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero
