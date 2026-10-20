namespace P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero

set_option autoImplicit false

namespace HeckeEis

p2m_open

open MvPolynomial CongruenceSubgroup

open scoped MatrixGroups

namespace TorsionFreeAux

theorem trace_sq_gammaL (N : ℕ) : (((gammaL N : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [coe_gammaL, coe_lowerSL, Matrix.trace_fin_two_of]; norm_num

end TorsionFreeAux
end HeckeEis
end P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero
