@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace AlgebraicGeometry.RingedSpace

universe u

/-- A small indexed open cover of a ringed space. The family may be empty when the source
is empty, and any member of the family may itself be empty. -/
structure OpenCover (X : RingedSpace.{u, u}) where
  /-- The type indexing the members of the cover. -/
  J : Type u
  /-- The indexed open subsets of the underlying topological space. -/
  U : J → Opens X
  /-- Each point of the source belongs to some member. -/
  covers : ∀ x : X, ∃ i, x ∈ U i

end AlgebraicGeometry.RingedSpace
end
