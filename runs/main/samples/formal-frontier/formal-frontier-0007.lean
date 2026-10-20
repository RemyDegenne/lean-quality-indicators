@[expose] public section

open CategoryTheory

open scoped TensorProduct ChangeOfRings

universe uR uK uM uN uP

namespace TopModuleCat

section Basic

variable (R : Type uR) (K : Type uK)

variable [CommRing R] [Ring K] [Algebra R K] [TopologicalSpace R]

variable [TopologicalSpace K] [DiscreteTopology K]

@[simp]
theorem discreteExtendScalars_obj (M : TopModuleCat.{uM} R) :
    (discreteExtendScalars R K).obj M = discreteExtendScalarsObj R K M := rfl

end Basic
end TopModuleCat
end
