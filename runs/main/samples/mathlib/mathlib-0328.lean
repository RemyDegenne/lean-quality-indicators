@[expose] public section

open Set Topology

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Preirreducible

@[stacks 004W "(2)"]
theorem isClosed_of_mem_irreducibleComponents (s) (H : s ∈ irreducibleComponents X) :
    IsClosed s := by
  rw [← closure_eq_iff_isClosed, eq_comm]
  exact subset_closure.antisymm (H.2 H.1.closure subset_closure)

end Preirreducible
end
