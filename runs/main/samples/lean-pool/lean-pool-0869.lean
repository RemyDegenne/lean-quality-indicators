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

open LocallyFiniteTriangleComplex PolygonalReplacementSourceAtlas RelativeSynchronizedTarget

namespace PolygonalReplacementSourceAtlas

theorem levelFaceParentPlaneAffine_injective
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) :
    Function.Injective (levelFaceParentPlaneAffine K s) := by
  apply affineMap_injective_of_injOn_convexHull
    standardTriangleVertex standardTriangleVertex_affineIndependent
  rw [← standardTrianglePlaneComplex_support]
  exact levelFaceParentPlaneAffine_injOn K s

end PolygonalReplacementSourceAtlas
end PartialTriangulation
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
