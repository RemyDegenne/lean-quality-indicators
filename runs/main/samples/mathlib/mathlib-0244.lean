public section

open Set Filter Function Topology

variable {α β : Type*} [TopologicalSpace α]

theorem nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x ≤ 𝓝[t] x ↔ t ∈ 𝓝[s] x :=
  eventuallySubset_iff_inf_principal_le.symm.trans eventuallySubset_iff_mem_inf_principal

end
