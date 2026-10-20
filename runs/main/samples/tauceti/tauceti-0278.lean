public section

open Filter Topology

namespace TauCeti

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]

section Separated

variable [ContinuousAdd M] [IsLinearTopology R M] [T1Space M]

theorem IsLinearTopology.eq_zero_of_forall_mem_of_isOpen {x : M}
    (h : ∀ N : Submodule R M, IsOpen (N : Set M) → x ∈ N) : x = 0 := by
  by_contra hx
  obtain ⟨N, hN, hNx⟩ := (IsLinearTopology.hasBasis_open_submodule R (M := M)).mem_iff.mp
    (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr (Ne.symm hx)))
  exact hNx (h N hN) rfl

end Separated
end TauCeti
end
