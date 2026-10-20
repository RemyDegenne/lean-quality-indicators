@[expose] public section

open scoped TensorProduct

universe uR uC uM uN uD uM' uN'

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

theorem tensorProdLeft_toLinearEquiv
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R) :
  (tensorProdLeft R C D M).toLinearEquiv =
    (show tensorLeftObj R (ModuleCat.of R (C × D)) M ≃ₗ[R]
      (tensorLeftObj R C M × tensorLeftObj R D M) from
        TensorProduct.prodLeft R R C D M) := by
  rfl

end TopModuleCat
end
