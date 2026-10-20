public section

open Filter Topology ZeroAtInftyContinuousMap

open scoped ZeroAtInfty ENNReal

variable {I J K R : Type*} [TopologicalSpace I] [TopologicalSpace J] [DiscreteTopology J]
  [DecidableEq J]

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

section NormedRing

variable [NormedRing R]

theorem matrixCoeff_injective :
    Function.Injective (matrixCoeff : (C₀(J, R) →L[R] C₀(I, R)) → Matrix I J R) := by
  intro u v h
  refine continuousLinearMap_ext_single_one fun j ↦ ?_
  ext i
  exact congr_fun₂ h i j

end NormedRing
end ContinuousLinearMap
end
