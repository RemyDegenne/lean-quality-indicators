@[expose] public section

open OrderDual

variable {F α β γ δ : Type*}

infixr:25 " →o " => OrderHom

infixl:25 " ↪o " => OrderEmbedding

infixl:25 " ≃o " => OrderIso

export OrderIsoClass (map_le_map_iff)

namespace OrderHom

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

variable {ι : Type*} {π : ι → Type*} [∀ i, Preorder (π i)]

/-- Construct a bundled monotone map `α →o Π i, π i` from a family of monotone maps
`f i : α →o π i`. -/
@[simps]
def pi (f : ∀ i, α →o π i) : α →o ∀ i, π i :=
  ⟨fun x i => f i x, fun _ _ h i => (f i).mono h⟩

end OrderHom
end
