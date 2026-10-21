namespace OAI

noncomputable section

open scoped BigOperators Topology

namespace Problem336.FiniteKernelBridge

open CoordinateTruncation

theorem transfer_entry_eq_finiteKernel {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1) (e f : finiteCodeEdges K) :
    TransferProjection.transferMatrix (ReducedCycleKernel.reducedFiniteIncidence K root) e f =
      inner ℝ (FreeKernel.edgeVector e.1)
        (FreeKernel.finiteKernel K (FreeKernel.edgeVector f.1)) := by
  rw [ReducedCycleKernel.finite_transfer_entry_eq_projection hK root,
    embedding_projection]
  rfl

end Problem336.FiniteKernelBridge
end
end OAI
