@[expose] public section

open scoped TensorProduct

universe uR uC uM

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

theorem tensorQuotient_toLinearEquiv (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    (P : Submodule R M) :
    (tensorQuotient R C M P).toLinearEquiv = TensorProduct.tensorQuotientEquiv C P := by
  rfl

end TopModuleCat
end
