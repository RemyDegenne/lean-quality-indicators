@[expose] public section

open scoped TensorProduct

universe uR uC uD uM uN uP uι

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

variable {C : ModuleCat.{uC} R} {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}

@[simp]
theorem tensorHomLinearEquiv_apply (f : tensorLeftObj R C M →L[R] N) :
    tensorHomLinearEquiv R C M N f = tensorCurry R f := by
  rfl

end TopModuleCat
end
