@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe uR uC uD uE uM uN uP uι uκ uI

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

section Coordinates

variable (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)

variable {ι : Type uι} [Finite ι]

@[simp]
theorem tensorCoordinateLinearEquiv_tensorGenerator_apply (b : Module.Basis ι R C)
    (c : C) (m : M) (i : ι) :
    tensorCoordinateLinearEquiv R C M b (tensorGenerator R C M c m) i = b.repr c i • m := by
  calc
    tensorCoordinateLinearEquiv R C M b (tensorGenerator R C M c m) i =
        tensorCoordinateLinearEquiv R C M b (c ⊗ₜ[R] m) i :=
      congrArg (fun x : tensorLeftObj R C M ↦ tensorCoordinateLinearEquiv R C M b x i)
        (tensorGenerator_apply R C M c m)
    _ = b.repr c i • m := tensorCoordinateLinearEquiv_tmul_apply R C M b c m i

end Coordinates
end TopModuleCat
end
