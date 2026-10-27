@[expose] public section

open scoped Manifold

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

open InvarianceOfDomain

attribute [instance] PartialTriangulation.vertexFintype

attribute [instance] PartialTriangulation.vertexDecidableEq

namespace PartialTriangulation

variable {S : Type*} [TopologicalSpace S] (T : PartialTriangulation S)

/-- On each maximal triangle, the ambient manifold boundary is one exposed simplicial face of
dimension at most one.

This is the missing regularity behind the bordered Moise argument.  Merely asking for the
boundary to be an edge subcomplex permits an interior chord joining two boundary vertices.  An
arbitrary convex-hull polygonalization can flatten such a chord onto the model boundary.  The
facewise condition rules that out and is stable under affine subdivision: the pullback of its
supporting face to every new triangle is again empty, a vertex, or an edge. -/
def BoundaryFacewiseRegular [ChartedSpace (EuclideanHalfSpace 2) S] : Prop :=
  ∀ t ∈ T.faces, ∃ b : Finset T.Vertex,
    b ⊆ t ∧ b.card ≤ 2 ∧
      ∀ x : T.toIntrinsic.realization, x ∈ T.toIntrinsic.faceCarrier t →
        (T.embed x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
          x ∈ T.toIntrinsic.faceCarrier b)

end PartialTriangulation
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
