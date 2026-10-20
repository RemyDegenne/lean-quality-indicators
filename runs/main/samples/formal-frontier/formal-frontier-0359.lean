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

theorem mapLinear_rViewHomeomorph_apply
    {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (x : discreteExtendScalarsRObj R K M) :
    mapLinear R K g (rViewHomeomorph R K M x) =
      rViewHomeomorph R K N (mapRCLM R K g x) := by
  exact (congrFun (tensorMap_rViewHomeomorph R K g) (rViewHomeomorph R K M x)).trans
    (congrArg (fun z : discreteExtendScalarsRObj R K M ↦
      rViewHomeomorph R K N (mapRCLM R K g z))
        ((rViewHomeomorph R K M).symm_apply_apply x))

end DiscreteExtendScalars
end Basic
end TopModuleCat
end
