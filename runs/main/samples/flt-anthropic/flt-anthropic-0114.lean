namespace P2MW.S_HeckeEis_linearIndependent_coeffH1par_map_rat_complex

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

namespace HeckeEis

namespace CoeffMapAux

p2m_open

open MvPolynomial

open scoped MatrixGroups

variable {R R' : Type*} [CommRing R] [CommRing R']

theorem coeff_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) (d : Fin 2 →₀ ℕ) :
    coeff d (binarySubst R M P) = ∑ d' ∈ P.support, (substCoeff M d d' : R) * coeff d' P := by
  conv_lhs => rw [P.as_sum, map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [show monomial d' (coeff d' P) = C (coeff d' P) * monomial d' 1 by rw [C_mul_monomial, mul_one], map_mul, binarySubst_C,
    coeff_C_mul, binarySubst_monomial_one, coeff_map, substCoeff, mul_comm]
  rfl

end CoeffMapAux
end HeckeEis
end
end P2MW.S_HeckeEis_linearIndependent_coeffH1par_map_rat_complex
