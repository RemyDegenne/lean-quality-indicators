@[expose] public section

universe u v w u₁

namespace DirectSum

open DirectSum Finsupp Module

section General

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable (R ι M)

section DecidableEq

variable [DecidableEq ι]

variable {ι M}

variable {R}

variable {N : Type u₁} [AddCommMonoid N] [Module R N]

variable (φ : ∀ i, M i →ₗ[R] N)

variable (R ι N)

/-- The linear map constructed using the universal property of the coproduct. -/
def toModule : (⨁ i, M i) →ₗ[R] N :=
  DFunLike.coe (DFinsupp.lsum ℕ) φ

end DecidableEq
end General
end DirectSum
end
