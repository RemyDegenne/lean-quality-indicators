public section

open Metric Set Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X]
  {D : Set X} {C : Set X} [RelCWComplex C D]

variable [T2Space X] (C)

/-- The `n`-th stage of the skeletal filtration, as an object of `TopCat`. -/
abbrev skeletonObj (n : ℕ) : TopCat.{w} := TopCat.of (skeletonLT C (n : ℕ∞) : Set X)

end TauCeti
end
