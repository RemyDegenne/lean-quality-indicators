@[expose] public section

open Fintype Function

universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V) {n : ℕ}

variable {G}

variable {ι α β : Type*} (C : G.Coloring α)

variable (G) in
/-- There is a noncomputable embedding of `α`-colorings to `β`-colorings if
`β` has at least as large a cardinality as `α`. -/
noncomputable def recolorOfCardLE {α β : Type*} [Fintype α] [Fintype β]
    (hn : Fintype.card α ≤ Fintype.card β) : G.Coloring α ↪ G.Coloring β :=
  G.recolorOfEmbedding (Function.Embedding.nonempty_of_card_le hn).some

end SimpleGraph
end
