@[expose] public section

noncomputable section

open LinearMap Module

open scoped TensorProduct

section CommSemiring

variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M]
  [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

section

variable [DecidableEq ι] [DecidableEq κ]

variable (ℬ : Basis ι R M) (𝒞 : Basis κ R N) (x : M ⊗[R] N)

/--
If `{ℬᵢ}` is a basis for the module `M`, then every elements of `x ∈ M ⊗ N` can be uniquely written
as `∑ᵢ ℬᵢ ⊗ nᵢ` for some `nᵢ ∈ N`.
-/
def TensorProduct.equivFinsuppOfBasisLeft : M ⊗[R] N ≃ₗ[R] ι →₀ N :=
  TensorProduct.comm R M N ≪≫ₗ TensorProduct.equivFinsuppOfBasisRight ℬ

end
end CommSemiring
end
end
