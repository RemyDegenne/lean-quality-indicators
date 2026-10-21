namespace OAI

noncomputable section

open Matrix Set

open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets

theorem upperRootParam_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (upperRootParam n) :=
  (emptyEliminationHomeomorph n).isOpenEmbedding.comp
    (completeRootChain n).param_isOpenEmbedding

end DukePrimeDegree
end
end OAI
