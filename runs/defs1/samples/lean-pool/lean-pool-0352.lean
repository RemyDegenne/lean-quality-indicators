@[expose] public section

namespace KaltonPeck.Support.GraphFredholm

noncomputable
section

open Coordinates Symplectic

open Function Set Filter Topology

open StrictlySingular

open scoped ENNReal NNReal Topology lp BigOperators InnerProductSpace

universe uX uY

variable {X : Type uX} {Y : Type uY}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

namespace Canonical

/-- Abbreviation for the canonical real Kalton--Peck space. -/
abbrev KP := CanonicalRealKaltonPeck

end Canonical
end
end KaltonPeck.Support.GraphFredholm
end
