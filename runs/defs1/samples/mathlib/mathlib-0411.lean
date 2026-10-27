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

variable {ι N φ}

variable (ψ : (⨁ i, M i) →ₗ[R] N)

variable {ψ} {ψ' : (⨁ i, M i) →ₗ[R] N}

/-- The inclusion of a subset of the direct summands
into a larger subset of the direct summands, as a linear map. -/
def lsetToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, M i) →ₗ[R] ⨁ i : T, M i :=
  toModule R _ _ fun i ↦ lof R T (fun i : T ↦ M i) ⟨i, H i.prop⟩

end DecidableEq
end General
end DirectSum
end
