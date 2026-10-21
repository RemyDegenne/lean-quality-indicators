namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

@[simp] theorem directionalLieDerivation_apply [Fintype σ]
    (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalLieDerivation h p = directionalDerivative h p := rfl

end Erdos3.VectorPolynomial
end
end OAI
