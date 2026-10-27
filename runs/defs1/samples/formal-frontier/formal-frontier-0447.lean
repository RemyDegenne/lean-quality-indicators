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

/-- The coefficient-linear tensor map inherits continuity from `mapRCLM`
through the identical topologies. Its target universe is independent. -/
noncomputable def mapCLM {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
    (g : M →L[R] N) : discreteExtendScalarsObj R K M →L[K]
      discreteExtendScalarsObj R K N where
  toLinearMap := mapLinear R K g
  cont := by
    refine (show Continuous (fun x : discreteExtendScalarsObj R K M ↦ mapLinear R K g x)
      from ?_)
    exact (((rViewHomeomorph R K N).continuous.comp (mapRCLM R K g).continuous).comp
      (rViewHomeomorph R K M).symm.continuous).congr
        (fun x : discreteExtendScalarsObj R K M ↦
          (congrFun (tensorMap_rViewHomeomorph R K g) x).symm)

end DiscreteExtendScalars
end Basic
end TopModuleCat
end
