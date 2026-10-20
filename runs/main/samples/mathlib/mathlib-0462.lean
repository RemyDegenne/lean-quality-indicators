@[expose] public section

noncomputable section

open Set Function Finset Finsupp AddMonoidAlgebra

variable {R M : Type*} [CommSemiring R]

namespace MvPolynomial

variable {σ : Type*}

section AddCommMonoid

variable [AddCommMonoid M]

variable (R)

variable {R}

variable (R)

namespace IsWeightedHomogeneous

variable {R}

variable {φ ψ : MvPolynomial σ R} {m n : M}

theorem add {w : σ → M} (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ + ψ) n :=
  (weightedHomogeneousSubmodule R w n).add_mem hφ hψ

end IsWeightedHomogeneous
end AddCommMonoid
end MvPolynomial
end
end
