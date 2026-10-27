@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

/-- The canonical one-point space, lifted into an arbitrary universe. -/
abbrev onePointSpace.{v} : TopCat.{v} := TopCat.of (ULift.{v} PUnit)

end TopCat
end
end
