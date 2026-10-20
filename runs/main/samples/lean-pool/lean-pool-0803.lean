@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ActiveTerminalBranchData

variable {F : Forest V}

theorem growth_terminal_edges_nonempty_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growth e).terminal.edges.Nonempty := by
  have hsplit :=
    (cons_mem_edgeOrders_iff (data.growth e).terminal).mp
      (data.growth_order_mem_edgeOrders_emptyStart e)
  exact ⟨e.val, hsplit.1⟩

end ActiveTerminalBranchData
end Forest
end BKAR
end
end
