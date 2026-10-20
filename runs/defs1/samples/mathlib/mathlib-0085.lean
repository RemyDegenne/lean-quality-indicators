@[expose] public section

noncomputable section

open Set Function Finsupp AddMonoidAlgebra

open scoped Pointwise

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (R σ)

variable {R σ}

variable (σ R)

/-- `fun s ↦ monomial s 1` as a homomorphism. -/
def monomialOneHom : Multiplicative (σ →₀ ℕ) →* MvPolynomial σ R :=
  AddMonoidAlgebra.of _ _

end CommSemiring
end MvPolynomial
end
end
