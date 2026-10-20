public section

namespace MvPolynomial

variable {K σ τ : Type*} [Field K] [Height.AdmissibleAbsValues K]

/-- The relative projective multiplicative height of a multivariate coefficient vector. -/
noncomputable def mulHeight (p : MvPolynomial σ K) : ℝ :=
  (AddMonoidAlgebra.coeff p).mulHeight

end MvPolynomial
end
