@[expose] public section

universe uR uM uM' uM'' uN uN' uN'' uI uP uL

namespace BalancedTensorProduct

variable {R : Type uR} [Ring R]

variable {M : Type uM} {M' : Type uM'} {M'' : Type uM''}

variable {N : Type uN} {N' : Type uN'} {N'' : Type uN''}

variable [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']

variable [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']

variable [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module Rᵐᵒᵖ M'']

variable [Module R N] [Module R N'] [Module R N'']

theorem mapLeft_mapRight (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') :
    (mapLeft (N := N') f).comp (mapRight (M := M) g) =
      (mapRight (M := M') g).comp (mapLeft (N := N) f) := by
  apply hom_ext
  intro m n
  rfl

end BalancedTensorProduct
end
