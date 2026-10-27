public section

variable {α β : Type*} {x y : α} {e : β} {G H : Graph α β} {F F₀ : Set β} {X : Set α}

open Set

namespace Graph

/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case) -/
@[expose, simps! (attr := grind =) vertexSet isLink]
protected def induce (G : Graph α β) (X : Set α) : Graph α β where
  vertexSet := X
  IsLink e x y := G.IsLink e x y ∧ x ∈ X ∧ y ∈ X
  isLink_symm := by simp +contextual [symm_def, G.isLink_comm]
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1

end Graph
end
