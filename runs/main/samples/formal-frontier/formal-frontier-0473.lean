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

theorem mapCLM_rViewHomeomorph_apply
    {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) (x : discreteExtendScalarsRObj R K M) :
    mapCLM R K g (rViewHomeomorph R K M x) =
      rViewHomeomorph R K N (mapRCLM R K g x) :=
  mapLinear_rViewHomeomorph_apply R K g x

end DiscreteExtendScalars
end Basic
end TopModuleCat
end
