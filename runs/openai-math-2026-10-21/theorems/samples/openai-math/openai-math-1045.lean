namespace OAI

section

namespace Erdos3

theorem polynomialCoordinateSlice_selected_coefficient {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (m : Fin (n + 1) →₀ ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ n p).coeff (m 0)).coeff m.tail =
      p.coeff m := by
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail]

end Erdos3
end
end OAI
