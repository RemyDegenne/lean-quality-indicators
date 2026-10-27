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

/-- The old outer graph realized on the wild source curve. -/
abbrev outerGraph (_w : Q.LocalOverlayRelabeling p s epsilon extra) : Graph Plane γ :=
  P.str.outerGraph.map P.src.pos

end LocalOverlayRelabeling
end SourceNonboundarySegmentCover
end Schoenflies
end
