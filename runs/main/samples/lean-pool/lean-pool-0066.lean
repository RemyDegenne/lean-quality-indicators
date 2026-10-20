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

theorem sourceNonboundaryGraph_edge_mem {e : γ} (he : e ∈ E(P.str.skel))
    (heOuter : e ∉ E(P.str.outerGraph)) :
    e ∈ E(P.sourceNonboundaryGraph) := by
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have habSrc := hab.map P.src.pos
  have heSrc : e ∈ E(P.src.graph) := by rwa [P.src.edgeSet_graph]
  have hdeleted : (P.src.graph.deleteEdges E(P.str.outerGraph)).IsLink
      e (P.src.pos a) (P.src.pos b) := by
    rw [← Graph.restrict_edgeSet_sdiff_eq_deleteEdges, Graph.restrict_isLink]
    exact ⟨⟨heSrc, heOuter⟩, habSrc⟩
  have ha : P.src.pos a ∈ P.sourceNonboundaryVertices :=
    ⟨e, heSrc, heOuter, habSrc.inc_left⟩
  have hb : P.src.pos b ∈ P.sourceNonboundaryVertices :=
    ⟨e, heSrc, heOuter, habSrc.inc_right⟩
  exact ⟨P.src.pos a, P.src.pos b, hdeleted, ha, hb⟩

end SourceNonboundarySegmentCover
end Schoenflies
end
