@[expose] public section

open CategoryTheory

open scoped TensorProduct ChangeOfRings

universe uR uK uM uN uP

namespace TopModuleCat

section Basic

variable (R : Type uR) (K : Type uK)

variable [CommRing R] [Ring K] [Algebra R K] [TopologicalSpace R]

variable [TopologicalSpace K] [DiscreteTopology K]

namespace DiscreteExtendScalars

theorem rViewHomeomorph_scalar (M : TopModuleCat.{uM} R) (k : K)
    (x : discreteExtendScalarsRObj R K M) :
    @Eq (discreteExtendScalarsObj R K M)
      (rViewHomeomorph R K M (scalar R K M k x))
      (@SMul.smul K (discreteExtendScalarsObj R K M)
        (discreteExtendScalarsObj R K M).toModuleCat.isModule.toSMul k
        (rViewHomeomorph R K M x)) := rfl

end DiscreteExtendScalars
end Basic
end TopModuleCat
end
