@[expose] public section

universe u v

namespace SimpleGraph

variable {ι : Sort*} {V : Type u} {W : Type v}

namespace Subgraph

variable {G : SimpleGraph V} {G₁ G₂ : G.Subgraph} {a b : V}

theorem degree_pos_iff_exists_adj {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    0 < G'.degree v ↔ ∃ w, G'.Adj v w := by
  simp only [degree, Fintype.card_pos_iff, nonempty_subtype, mem_neighborSet]

end Subgraph
end SimpleGraph
end
