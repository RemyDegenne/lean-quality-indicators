public section

open Set

variable {α β γ : Type*} {x y : α} {e e' f : Set α}

namespace Hypergraph

variable {H : Hypergraph α}

scoped notation "V(" H ")" => Hypergraph.vertexSet H

scoped notation "E(" H ")" => Hypergraph.edgeSet H

/-- A vertex is isolated if it is not incident to any edges (including loops). -/
@[expose]
def IsIsolated (H : Hypergraph α) (x : α) : Prop := ∀ e ∈ E(H), x ∉ e

end Hypergraph
end
