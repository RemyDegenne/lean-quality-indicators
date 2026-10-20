@[expose] public section

open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {e f : β} {x y : α}

/-- `G.degree x` is the number of edge ends of `G` at the vertex `x`: a non-loop edge
incident with `x` contributes one, a loop at `x` contributes two. -/
noncomputable def degree (G : Graph α β) (x : α) : ℕ :=
  (G.incidenceSet x).ncard + (G.loopSet x).ncard

end Graph
end
