@[expose] public section

open Filter

open scoped BigOperators Topology

namespace LocalComplexGeometry

noncomputable section

/-- The prepared value at `z`, regarded as a polynomial in the last variable. -/
def preparedPolynomialAt {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n) :
    Polynomial ℂ :=
  Polynomial.X ^ d +
    ∑ i : Fin d, Polynomial.C (a i z) * Polynomial.X ^ (i : ℕ)

end
end LocalComplexGeometry
end
