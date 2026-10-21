namespace OAI

noncomputable section

namespace Problem336

namespace FiniteEncoding

lemma isTree_graph_treeCode {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {T : Finset (ℕ × ℕ)}
    (hT : TreeOn K T) : (graph (K.1,T)).IsTree := by
  have hc := finiteConnected_treeCode hK hT
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connected hc, ?_⟩
  rw [← card_edgePairs, edgePairs_graph hc]
  simpa [Nat.card_eq_fintype_card] using hT.2.1

end FiniteEncoding
end Problem336
end
end OAI
