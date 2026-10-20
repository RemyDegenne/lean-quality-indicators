namespace P2MW.S_Polynomial_exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero

set_option autoImplicit false

theorem solution
    {A : Type*} [CommRing A] (s : Polynomial A) (hs : IsUnit (s.coeff 0)) (m : ℕ) :
    ∃ σ : Fin (m + 1) → A,
      ∀ r : Fin (m + 1), ((∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (σ r')) * s - 1).coeff r = 0 :=
  InvJet.exists_inv_jet s hs m

end P2MW.S_Polynomial_exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero
