namespace P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit

set_option autoImplicit false

open scoped Quaternion TensorProduct

open IsDedekindDomain NumberField

namespace R4EmbedM2

variable {a b : ℚ}

section Division

variable {K : Type*} [Field K] [Algebra ℚ K]

noncomputable def retr (ψ : Module.Dual ℚ K) : ℍ[ℚ, a, b] ⊗[ℚ] K →ₗ[ℚ] ℍ[ℚ, a, b] :=
  (TensorProduct.rid ℚ ℍ[ℚ, a, b]).toLinearMap ∘ₗ LinearMap.lTensor ℍ[ℚ, a, b] ψ

end Division
end R4EmbedM2
end P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit
