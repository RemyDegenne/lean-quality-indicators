@[expose] public section

namespace Contrib.MaxFlowMinCut

section Network

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem value_le_capacity {Net : Network N} (F : Flow Net) (C : Cut Net) :
    F.value ≤ C.capacity := by
  rw [F.value_eq_flow_across C]
  unfold Cut.capacity
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact F.capacitated u v

end Network
end Contrib.MaxFlowMinCut
end
