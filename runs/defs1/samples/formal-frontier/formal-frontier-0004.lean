@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

/-- The canonical empty space, lifted into an arbitrary universe. -/
abbrev emptySpace.{v} : TopCat.{v} := TopCat.of (ULift.{v} Empty)

end TopCat
end
end
