@[expose] public section

open scoped TensorProduct

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

open scoped InnerProductSpace

local notation x" ⊗ₘ "y => TensorProduct.map x y

open Matrix

open Kronecker

open scoped FiniteDimensional

theorem TensorProduct.ring_tmul {R : Type*} [CommRing R] (x : R ⊗[R] R) :
  ∃ (a b : R), x = a ⊗ₜ[R] b := by
  refine ⟨1, TensorProduct.lid R R x, ?_⟩
  rw [← TensorProduct.lid_symm_apply]
  exact (TensorProduct.lid R R).symm_apply_apply x |>.symm

end
