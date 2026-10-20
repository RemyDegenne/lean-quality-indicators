public section

namespace TauCeti

open _root_.Quiver

universe u

namespace DoubledQuiver

variable {V : Type u} (G : SimpleGraph V)

/-- Convert a path in the doubled quiver between graph-labelled vertices to a graph walk. -/
def pathToWalk {i j : V} (p : Quiver.Path (vertex G i) (vertex G j)) : G.Walk i j := by
  exact (pathToWalkAux G p).copy
    (vertexEquiv_symm_vertex G i) (vertexEquiv_symm_vertex G j)

end DoubledQuiver
end TauCeti
end
