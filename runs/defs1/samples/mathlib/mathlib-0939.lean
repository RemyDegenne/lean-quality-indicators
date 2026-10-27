@[expose] public section

namespace SimpleGraph

variable {U U' V V' W W' γ : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph U}
  {G' : SimpleGraph V'} {H' : SimpleGraph W'} {I' : SimpleGraph U'} {v v' : V} {w w' : W}

@[inherit_doc] infixl:60 " ⊕g " => SimpleGraph.sum

/-- Get coloring of `G` from coloring of `G ⊕g H` -/
def Coloring.sumLeft (c : (G ⊕g H).Coloring γ) : G.Coloring γ := c.comp Embedding.sumInl.toHom

end SimpleGraph
end
