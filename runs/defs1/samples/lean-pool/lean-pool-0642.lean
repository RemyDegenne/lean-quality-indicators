@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace PlaneComplex

variable (K : PlaneComplex)

/-- A polygonal replacement for one trimmed central arc, kept inside its assigned tube. -/
structure CentralPolygonalArc {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont D)
    (i : Fin (Fintype.card K.EdgeFace)) where
  /-- The `data` declaration. -/
  data : BrokenLineData
    (Metric.thickening C.radius (K.edgeTrim hcont D i).centralCarrier ∩
      convexHull ℝ (h '' K.cellCarrier (K.edgeAt i).1))
  start_eq : data.start = K.edgeCurve h i (K.edgeTrim hcont D i).left
  finish_eq : data.finish = K.edgeCurve h i (K.edgeTrim hcont D i).right

end PlaneComplex
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
