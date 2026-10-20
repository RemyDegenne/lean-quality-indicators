@[expose] public section

noncomputable section

open Polynomial Set Function Finsupp AddMonoidAlgebra

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type*} {a : R} {e : ℕ} {s : σ →₀ ℕ}

section Equiv

variable (R) [CommSemiring R]

section

variable (S₁ S₂ S₃)

section commAlgEquiv

variable {R S₁ S₂ : Type*} [CommSemiring R]

variable (R S₁ S₂) in
/-- The algebra isomorphism between multivariable polynomials in variables `S₁` of multivariable
polynomials in variables `S₂` and multivariable polynomials in variables `S₂` of multivariable
polynomials in variables `S₁`. -/
noncomputable
def commAlgEquiv : MvPolynomial S₁ (MvPolynomial S₂ R) ≃ₐ[R] MvPolynomial S₂ (MvPolynomial S₁ R) :=
  AddMonoidAlgebra.commAlgEquiv _

end commAlgEquiv
end
end Equiv
end MvPolynomial
end
end
