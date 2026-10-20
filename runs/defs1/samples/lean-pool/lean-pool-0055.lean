@[expose] public section

namespace Sabidussi

namespace LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

variable {V E : Type*} [Fintype V] [Fintype E]

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)

/-- The ordinary natural-number degree of `v` in an edge set. Edge ends are counted, so this
definition also has the standard behavior for multigraphs. -/
def degreeIn (F : Finset E) (v : V) : ℕ :=
  ((F ×ˢ (Finset.univ : Finset (Fin 2))).filter fun h ↦ G.endAt h.1 h.2 = v).card

end LoopMultigraph
end Sabidussi
end
