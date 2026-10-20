@[expose] public section

open Set Topology

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace GeometricTriangulation

variable {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)

theorem polygonalRealization_homeomorphic
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces) :
    Nonempty
      (T.toFiniteCyclicPresentation.PolygonalRealization valid ≃ₜ
        T.realization) :=
  ⟨T.polygonalRealizationHomeomorph valid hstar⟩

end GeometricTriangulation
end ClassificationOfSurfaces
end Topology
end LeanEval
end
