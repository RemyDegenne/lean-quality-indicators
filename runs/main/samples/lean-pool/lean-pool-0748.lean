@[expose] public section

open Set

open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}

namespace SourceNonboundarySegmentCover

variable (Q : SourceNonboundarySegmentCover P)

namespace LocalOverlayRelabeling

variable {Q : SourceNonboundarySegmentCover P} {p : Plane} {s epsilon : ℝ}
  {extra : List Plane} (w : Q.LocalOverlayRelabeling p s epsilon extra)

theorem inner_pointSet :
    Graph.pointSet w.innerGraph w.drawing =
      Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing := by
  calc
    Graph.pointSet w.innerGraph w.drawing =
        Graph.pointSet w.innerGraph
          ((Q.localOverlay p s epsilon extra).relabelDrawing w.name segmentDrawing) := by
      apply Graph.pointSet_congr
      intro e he
      simpa only [Graph.edgeArc] using congrArg (fun f : ℝ → Plane => f '' unitInterval)
        (w.drawing_of_inner he)
    _ = Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing :=
      Graph.pointSet_relabelEdges w.name_inj

end LocalOverlayRelabeling
end SourceNonboundarySegmentCover
end Schoenflies
end
