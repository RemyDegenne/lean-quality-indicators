public section

open Set Filter

open scoped Topology

section Preorder

variable {α : Type*} [TopologicalSpace α] [Preorder α]

@[to_dual]
theorem nhdsWithin_Ici_neBot {a b : α} (H₂ : a ≤ b) : NeBot (𝓝[Ici a] b) :=
  nhdsWithin_neBot_of_mem H₂

end Preorder
end
