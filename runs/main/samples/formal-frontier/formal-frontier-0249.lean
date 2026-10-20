@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe uR uC uD uE uM uN uP uι uκ uI

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

section TensorMaps

variable {C : ModuleCat.{uC} R} {D : ModuleCat.{uD} R} {E : ModuleCat.{uE} R}

variable {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R} {P : TopModuleCat.{uP} R}

theorem tensorMapBilinear_comp (f : C →ₗ[R] D) (f' : D →ₗ[R] E)
    (g : M →L[R] N) (g' : N →L[R] P) :
    tensorMapBilinear R C E M P (f'.comp f) (g'.comp g) =
      (tensorMapBilinear R D E N P f' g').comp (tensorMapBilinear R C D M N f g) := by
  simp only [tensorMapBilinear_apply, tensorMapCLM_comp]

end TensorMaps
end TopModuleCat
end
