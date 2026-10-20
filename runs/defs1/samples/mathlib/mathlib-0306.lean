@[expose] public section

open scoped TensorProduct

variable {R ι A B : Type*}

variable [CommSemiring ι] [DecidableEq ι]

variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)

variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

open DirectSum

namespace GradedTensorProduct

open TensorProduct

@[inherit_doc GradedTensorProduct]
scoped[TensorProduct] notation:100 𝒜 " ᵍ⊗[" R "] " ℬ:100 => GradedTensorProduct R 𝒜 ℬ

@[inherit_doc]
notation:100 x " ᵍ⊗ₜ " y:100 => tmul _ x y

@[inherit_doc]
notation:100 x " ᵍ⊗ₜ[" R "] " y:100 => tmul R x y

variable [Module ι (Additive ℤˣ)]

/-- The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps]
def includeLeftRingHom : A →+* 𝒜 ᵍ⊗[R] ℬ where
  toFun a := a ᵍ⊗ₜ 1
  map_zero' := by simp
  map_add' := by simp [tmul, TensorProduct.add_tmul]
  map_one' := rfl
  map_mul' a₁ a₂ := by
    classical
    rw [← DirectSum.sum_support_decompose 𝒜 a₂, Finset.mul_sum]
    simp_rw [tmul, sum_tmul, map_sum, Finset.mul_sum]
    congr
    ext i
    rw [← SetLike.coe_gOne ℬ, tmul_coe_mul_coe_tmul, zero_mul, uzpow_zero, one_smul,
      SetLike.coe_gOne, one_mul]

end GradedTensorProduct
end
