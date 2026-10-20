@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}

/-- The finite vertex-side condition used to establish graph-side compatibility. -/
def FaceFillingsVerticesAvoidClosedRegions : Prop :=
  ∀ (t : K.Face) (v : K.UsedVertex), v.1 ∉ t.1 →
    h (K.vertexPoint v) ∉
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion

end IntrinsicTwoComplex
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
