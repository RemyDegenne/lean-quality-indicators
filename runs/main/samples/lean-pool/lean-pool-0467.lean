@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace BrokenLineData

variable {U : Set Plane} (B : BrokenLineData U)

theorem segmentComplex_support (i : Fin B.n) :
    (B.segmentComplex i).support =
      segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) := by
  apply B.arrangementMesh.toPlaneComplex.restrictedTo_support_eq
  intro x hx
  obtain ⟨s, hs, hxs, hsseg⟩ := B.exists_face_on_segment i hx
  refine ⟨s, hs, hxs, ?_⟩
  apply convexHull_min _ (convex_segment _ _)
  rintro y ⟨v, hv, rfl⟩
  exact hsseg v hv

end BrokenLineData
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
