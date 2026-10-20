@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace PolygonalTheta

variable (G : PolygonalTheta)

namespace MeshCrosscut

variable {G : PolygonalTheta} {M : TriangleMesh} (C : G.MeshCrosscut M)

/-- Select the maximal triangles lying on the `J23` side of the crosscut. -/
noncomputable def side23Mesh (_ : G.MeshCrosscut M) : TriangleMesh := by
  classical
  exact M.restrictTriangles fun t =>
    (interior (M.triangleCarrier t) ∩ G.J23.interiorRegion).Nonempty

end MeshCrosscut
end PolygonalTheta
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
