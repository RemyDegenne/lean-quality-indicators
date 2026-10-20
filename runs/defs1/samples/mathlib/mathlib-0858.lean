@[expose] public section

open DirectSum

variable {ι R A σ : Type*}

section GradedAlgebra

variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]

variable (𝒜 : ι → Submodule R A)

variable [GradedAlgebra 𝒜]

open DirectSum

/-- The projection maps of graded algebra -/
def GradedAlgebra.proj (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (i : ι) : A →ₗ[R] A :=
  (𝒜 i).subtype.comp <| (DFinsupp.lapply i).comp (decomposeAlgEquiv 𝒜).toAlgHom.toLinearMap

end GradedAlgebra
end
