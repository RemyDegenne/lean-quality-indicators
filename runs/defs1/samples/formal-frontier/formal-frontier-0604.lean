@[expose] public section

open CategoryTheory

open scoped TensorProduct ChangeOfRings

universe uR uK uM uN uP

namespace TopModuleCat

section FiniteFieldSpecialization

namespace FiniteExtendScalars

/-- The base-linear view of finite-dimensional discrete-field scalar extension. -/
noncomputable def baseObj
    (R : Type uR) (K : Type uK) [Field R] [Field K] [Algebra R K]
    [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace K] [DiscreteTopology K]
    [FiniteDimensional R K] (M : TopModuleCat.{uM} R) : TopModuleCat.{max uK uM} R :=
  discreteExtendScalarsRObj R K M

end FiniteExtendScalars
end FiniteFieldSpecialization
end TopModuleCat
end
