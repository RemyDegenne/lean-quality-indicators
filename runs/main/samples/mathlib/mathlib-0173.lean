@[expose] public section

@[inherit_doc]
notation:25 𝒜 " →ₐᵍ[" R "] " ℬ => GradedAlgHom R 𝒜 ℬ

namespace GradedAlgHom

variable {R A B C D ι : Type*}
  [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B} {𝒞 : ι → Submodule R C} {𝒟 : ι → Submodule R D}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]

variable (f : 𝒜 →ₐᵍ[R] ℬ)

@[simp] theorem coe_mul (f g : 𝒜 →ₐᵍ[R] 𝒜) : ⇑(f * g) = f ∘ g := rfl

end GradedAlgHom
end
