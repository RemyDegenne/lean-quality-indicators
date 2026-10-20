public noncomputable section

open scoped NNReal unitInterval ContinuousMap

open Topology Set unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace MoorePath

/-- A Moore path, as a path on the unit interval between its end points. -/
def toPath (γ : MoorePath X) : Path γ.source γ.target where
  toContinuousMap := γ.toUnitPath
  source' := γ.toUnitPath_zero
  target' := γ.toUnitPath_one

end MoorePath
end TauCeti
end
