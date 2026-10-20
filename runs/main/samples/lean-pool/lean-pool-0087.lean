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

theorem patchTileFaceClosedRegion_subset_modelRegion
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (g' : U → k.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    PolygonalFamily.closedRegion A.patchTileFacePolygon ⊆ k.modelRegion := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
  have hxV : x ∈ k.perturbationRegion := Q.faceClosedRegion_subset f.1 hxf
  let z : k.perturbationRegion := ⟨x, hxV⟩
  have hzFace : z ∈ Q.complex.faceCarrier f.1 := by
    rw [Q.faceCarrier_eq f.1]
    exact hxf
  have hzSupport : z ∈ Q.complex.support :=
    Set.mem_iUnion.mpr ⟨f.1, hzFace⟩
  exact Q.support_subset_modelRegion_of_coordinate k g' hcoord hzSupport

end PolygonalReplacementSourceAtlas
end PartialTriangulation
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
