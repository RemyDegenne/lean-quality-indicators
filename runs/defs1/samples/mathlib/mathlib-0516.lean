@[expose] public section

open Function

variable {F α β γ δ : Type*}

/-- The type of Esakia morphisms, aka continuous pseudo-epimorphisms, from `α` to `β`. -/
structure EsakiaHom (α β : Type*) [TopologicalSpace α] [Preorder α] [TopologicalSpace β]
  [Preorder β] extends α →Co β where
  exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : toFun a ≤ b → ∃ c, a ≤ c ∧ toFun c = b

end
