public section

open Set Filter Function Topology

variable {α β : Type*} [TopologicalSpace α]

theorem nhdsWithin_inter' (a : α) (s t : Set α) : 𝓝[s ∩ t] a = 𝓝[s] a ⊓ 𝓟 t := by
  delta nhdsWithin
  rw [← inf_principal, inf_assoc]

end
