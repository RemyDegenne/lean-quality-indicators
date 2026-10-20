@[expose] public section

namespace MooreBound

open Set

namespace DegreeDiameter

open SimpleGraph

universe u

lemma lineGraphSharedVertex_mem_right {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) (f : G.lineGraph.neighborSet e) : lineGraphSharedVertex e f ∈ f.1.1 :=
  (Classical.choose_spec (SimpleGraph.lineGraph_adj_iff_exists.mp f.property).2).2

end DegreeDiameter
end MooreBound
end
