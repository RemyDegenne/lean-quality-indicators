@[expose] public section

variable {α β : Type*} {x y z u v w : α} {e f : β}

open Set

namespace Graph

variable {G H : Graph α β}

scoped notation "V(" G ")" => Graph.vertexSet G

scoped notation "E(" G ")" => Graph.edgeSet G

/-- Two graphs are compatible if their shared edges have the same ends in both graphs. -/
def Compatible (G H : Graph α β) : Prop :=
  ∀ ⦃e⦄, e ∈ E(G) → e ∈ E(H) → ∀ x y, G.IsLink e x y ↔ H.IsLink e x y

end Graph
end
