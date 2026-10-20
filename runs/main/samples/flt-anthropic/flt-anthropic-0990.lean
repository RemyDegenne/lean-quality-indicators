namespace P2MW.S_MvPolynomial_CrossingQuotient_minimalPrimes_span_algebraMap_eq_pair

set_option autoImplicit false

namespace CrossingResolutionBranch

open MvPolynomial MvPolynomial.CrossingQuotient

variable {W : Type*} [CommRing W] (s : W)

theorem exists_normalForm (f : CrossingQuotient W s) :
    ∃ p q : Polynomial W, f = Polynomial.aeval (U s) p + V s * Polynomial.aeval (V s) q := by
  obtain ⟨F, rfl⟩ := mk_surjective s f
  induction F using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Polynomial.C a, 0, ?_⟩
    simp only [Polynomial.aeval_C, map_zero, mul_zero, add_zero]
    exact mk_C_eq s a
  | add p q hp hq =>
    obtain ⟨p₁, q₁, h₁⟩ := hp
    obtain ⟨p₂, q₂, h₂⟩ := hq
    refine ⟨p₁ + p₂, q₁ + q₂, ?_⟩
    rw [map_add, h₁, h₂, map_add, map_add]
    ring
  | mul_X p i hp =>
    obtain ⟨P, Q, hPQ⟩ := hp
    have hxy := U_mul_V s
    fin_cases i
    · refine ⟨Polynomial.X * P + Polynomial.C (s * Q.coeff 0), Polynomial.C s * Q.divX, ?_⟩
      have hQ : Polynomial.aeval (V s) Q = V s * Polynomial.aeval (V s) Q.divX +
          algebraMap W _ (Q.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
        simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [map_mul, hPQ]
      simp only [Fin.zero_eta, Fin.isValue, map_add, map_mul, Polynomial.aeval_X,
        Polynomial.aeval_C]
      rw [hQ]
      change _ * U s = U s * _ + _ + _
      linear_combination (Polynomial.aeval (V s) Q.divX * V s + (algebraMap W _ (Q.coeff 0))) * hxy
    · refine ⟨Polynomial.C s * P.divX, Polynomial.C (P.coeff 0) + Polynomial.X * Q, ?_⟩
      have hP : Polynomial.aeval (U s) P = U s * Polynomial.aeval (U s) P.divX +
          algebraMap W _ (P.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add P]
        simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [map_mul, hPQ]
      simp only [Fin.mk_one, Fin.isValue, map_add, map_mul, Polynomial.aeval_X,
        Polynomial.aeval_C]
      rw [hP]
      change _ * V s = _
      linear_combination (Polynomial.aeval (U s) P.divX) * hxy

end CrossingResolutionBranch
end P2MW.S_MvPolynomial_CrossingQuotient_minimalPrimes_span_algebraMap_eq_pair
