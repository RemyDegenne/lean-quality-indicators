public section

open Set

open scoped Manifold ContDiff

namespace TauCeti

universe u

variable {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]

/-- A compact connected surface, allowing a nonempty boundary, in the standard Euclidean
half-space model. -/
def IsCompactConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] : Prop :=
  IsCompactConnectedManifold 2 S

end TauCeti
end
