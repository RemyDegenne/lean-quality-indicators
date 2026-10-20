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

variable {S : Type*} [TopologicalSpace S]

attribute [instance] PolygonalReplacementSourceAtlas.tileDecidableEq

namespace PolygonalReplacementPresentation

variable {X : Type*} [TopologicalSpace X] {V : Set Plane}

open LocallyFiniteTriangleComplex.PlaneGraphRealization

/-- The canonical source parametrization of one retained replacement face.  It is obtained by
pulling the replacement face parametrization back through the presentation homeomorphism, so it
uses exactly the same abstract barycentric coordinates as `Q.complex.faceMap`. -/
noncomputable def sourceFaceMap
    (Q : PolygonalReplacementPresentation X V) (f : Q.complex.Face) :
    Q.complex.ClosedFace f → X :=
  Q.sourceHomeomorph.symm ∘ faceToSupport (K := Q.complex) f

end PolygonalReplacementPresentation
end PartialTriangulation
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
