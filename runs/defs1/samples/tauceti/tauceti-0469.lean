public section

open Matrix MulOpposite

namespace MvPolynomial

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

/-- The linear change of variables `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ` given by a square matrix `M`. -/
noncomputable def linearSubst (M : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ ∑ j, C (M i j) * X j

end MvPolynomial
end
