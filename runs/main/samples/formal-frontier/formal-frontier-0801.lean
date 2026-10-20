@[expose] public section

open scoped TensorProduct

universe uR uC uD uM uN uP uι

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

variable {C : ModuleCat.{uC} R} {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}

theorem tensorLeft_ext_tensorGenerator {f g : tensorLeftObj R C M →L[R] N}
    (h : ∀ c : C, f.comp (tensorGenerator R C M c) =
      g.comp (tensorGenerator R C M c)) : f = g := by
  apply tensorLeft_ext R
  intro c m
  simpa only [ContinuousLinearMap.comp_apply, tensorGenerator_apply] using
    DFunLike.congr_fun (h c) m

end TopModuleCat
end
