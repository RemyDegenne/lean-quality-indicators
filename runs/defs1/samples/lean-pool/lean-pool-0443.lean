@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

namespace ThresholdPartition

/-- Restrict the supplied threshold partition to an induced subgraph. -/
def induce (P : ThresholdPartition G) (s : Set V) : ThresholdPartition (G.induce s) :=
  P.comap (Function.Embedding.subtype s)

end ThresholdPartition
end SimpleGraph
end
