public section

variable {α β : Type*} {x y u v : α} {e : β} {G G₁ G₂ H H₁ H₂ K : Graph α β} {F₁ F₂ : Set β}
  {X : Set α}

open Set

open scoped Sym2

namespace Graph

@[inherit_doc IsSpanningSubgraph]
infixl:50 " ≤s " => Graph.IsSpanningSubgraph

section InducedSubgraph

@[inherit_doc IsInducedSubgraph]
scoped infixl:50 " ≤i " => Graph.IsInducedSubgraph

lemma IsSubgraph.not_isInducedSubgraph_iff (hHG : H ≤ G) :
    ¬ H ≤i G ↔ ∃ e x y, G.IsLink e x y ∧ x ∈ V(H) ∧ y ∈ V(H) ∧ e ∉ E(H) := by
  contrapose!; symm
  exact ⟨fun hnind ↦ ⟨hHG, fun e x y hxy hx hy => hxy.anti_of_mem hHG (hnind e x y hxy hx hy)⟩,
    fun hind _ _ _ hexy hx hy ↦ hind.isLink_of_mem_mem hexy hx hy |>.edge_mem⟩

end InducedSubgraph
end Graph
end
