public section

open CategoryTheory

open scoped TensorProduct

universe u v w x y z

namespace Representation

variable {R : Type u} {D : Type v} {M : Type w}

variable [CommSemiring R] [Group D] [AddCommMonoid M] [Module R M]

variable {N : Type y} [AddCommMonoid N] [Module R N]

variable {ρ : Representation R D M} {τ : Representation R D N}

/-- Applying an intertwining map in every tensor factor intertwines the corresponding
wreath-product representations. -/
noncomputable def IntertwiningMap.wreathTensor (f : ρ.IntertwiningMap τ) (ι : Type x) :
    (ρ.wreathTensor ι).IntertwiningMap (τ.wreathTensor ι) where
  toLinearMap := PiTensorProduct.map fun _ ↦ f.toLinearMap
  isIntertwining' a := by
    ext m
    simp [wreathTensor_apply_tprod, f.isIntertwining]

end Representation
end
