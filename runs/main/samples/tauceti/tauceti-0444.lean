public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace ReducedTensorWords

variable (R : Type uR) {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R}

theorem rTensor_add_lTensor_rTensor_congr
    {b₁ b₂ τ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (P : Submodule R (ReducedTensorWords R M)) (h : ∀ z ∈ P, b₁ z = b₂ z) (w : P ⊗[R] P) :
    LinearMap.rTensor (ReducedTensorWords R M) b₁ (TensorProduct.mapIncl P P w) +
        LinearMap.lTensor (ReducedTensorWords R M) b₁
          (LinearMap.rTensor (ReducedTensorWords R M) τ (TensorProduct.mapIncl P P w)) =
      LinearMap.rTensor (ReducedTensorWords R M) b₂ (TensorProduct.mapIncl P P w) +
        LinearMap.lTensor (ReducedTensorWords R M) b₂
          (LinearMap.rTensor (ReducedTensorWords R M) τ (TensorProduct.mapIncl P P w)) := by
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
      rw [h _ u.2, h _ v.2]
  | add u v hu hv =>
      simp only [map_add]
      rw [add_add_add_comm, hu, hv, ← add_add_add_comm]

end ReducedTensorWords
end TauCeti
end
