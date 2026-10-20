@[expose] public section

open CategoryTheory

open scoped TensorProduct ChangeOfRings

universe uR uK uM uN uP

namespace TopModuleCat

section Rebundle

variable (R : Type uR) (K : Type uK)

variable [Ring R] [Ring K] [TopologicalSpace R] [TopologicalSpace K]

theorem withModule_toModuleCat (N : TopModuleCat.{uM} R) (moduleK : Module K N)
    (hcont : @ContinuousSMul K N moduleK.toSMul _ N.topologicalSpace) :
    (withModule R K N moduleK hcont).toModuleCat =
      @ModuleCat.of K _ N N.toModuleCat.isAddCommGroup moduleK := rfl

end Rebundle
end TopModuleCat
end
