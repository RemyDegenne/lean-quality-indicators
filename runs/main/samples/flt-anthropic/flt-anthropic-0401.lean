namespace P2MW.S_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv

set_option autoImplicit false

noncomputable section

namespace HeckeEis

namespace BolAux

p2m_open

open UpperHalfPlane MvPolynomial

open scoped MatrixGroups

variable {K : Type*} [CommRing K]

theorem coeff_pderiv_one (P : MvPolynomial (Fin 2) K) (d : Fin 2 →₀ ℕ) :
    coeff d (pderiv 1 P) = ((d 1 + 1 : ℕ) : K) * coeff (d + Finsupp.single 1 1) P := by
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases hs : s = d + Finsupp.single 1 1
    · subst hs
      simp only [add_tsub_cancel_right, ↓reduceIte, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      push_cast
      ring
    · rw [if_neg hs, mul_zero]
      split_ifs with h
      ·
        have hs1 : s 1 = 0 := by
          by_contra hne
          apply hs
          rw [← h]
          ext i
          fin_cases i
          · simp
          · simp only [Fin.mk_one, Fin.isValue, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same]
            omega
        simp [hs1]
      · rfl
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

end BolAux
end HeckeEis
end
end P2MW.S_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv
