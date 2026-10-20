@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

attribute [local instance] MvPolynomial.gradedAlgebra

theorem rncMap_isHomogeneous (R : Type u) [CommSemiring R] (n d : ℕ)
    (p : Source R n) (hp : p.IsHomogeneous d) :
    (rncMap R n p).IsHomogeneous (n * d) := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro t ht
  rw [rncMap_monomial]
  apply MvPolynomial.isHomogeneous_monomial
  have htdegree : sourceDegree n t = d := by
    change t.degree = d
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp ht)
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, rncExponent_total, htdegree]

end ToricIdeals.RationalNormalCurve
end
