namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem boundedArrayPolynomial_degreeLE {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (x : BoundedCoefficientExponent K h → W) :
    DegreeLE (1 : K → ℕ) h (boundedArrayPolynomial h x) := by
  intro e he
  rw [boundedArrayPolynomial, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro d _
  exact degreeLE_monomial_of_degree_le d.property (x d) e he

end Erdos3.VectorPolynomial
end
end OAI
