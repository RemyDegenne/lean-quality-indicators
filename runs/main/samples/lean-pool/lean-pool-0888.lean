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

namespace PolygonalReplacementSourceAtlas

theorem coordinatePreimage_subset_sourceTileFacesMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    {x : K.realization | ∃ hx : x ∈ U,
        (Q.sourceHomeomorph ⟨x, hx⟩).1 ∈ C} ⊆
      ⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1 := by
  rintro x ⟨hxU, hxC⟩
  let y := Q.sourceHomeomorph ⟨x, hxU⟩
  have hySelected := Q.support_inter_subset_iUnion_facesMeeting hC ⟨y.2, hxC⟩
  obtain ⟨f, hyFace⟩ := Set.mem_iUnion.mp hySelected
  let f' : A.TileFacesMeeting C hC :=
    ⟨f.1, A.faceMeeting_mem_tileFaceFinsetMeeting C hC f⟩
  apply Set.mem_iUnion.mpr
  exact ⟨f', hxU, hyFace⟩

end PolygonalReplacementSourceAtlas
end PartialTriangulation
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
