@[expose] public section

open scoped TensorProduct

universe uR uC uM uN uD uM' uN'

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

variable (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R) (N : TopModuleCat.{uN} R)

@[simp]
theorem tensorProdRight_symm_tmul (c : C) (m : M) (n : N) :
    (tensorProdRight R C M N).symm (c ⊗ₜ[R] m, c ⊗ₜ[R] n) =
      c ⊗ₜ[R] (m, n) := by
  rw [tensorProdRight_symm_apply]
  exact TensorProduct.prodRight_symm_tmul R R C M N c m n

end TopModuleCat
end
