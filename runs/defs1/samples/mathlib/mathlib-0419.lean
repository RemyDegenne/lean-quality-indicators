@[expose] public section

open OrderDual

variable {F α β γ δ : Type*}

infixr:25 " →o " => OrderHom

infixl:25 " ↪o " => OrderEmbedding

infixl:25 " ≃o " => OrderIso

export OrderIsoClass (map_le_map_iff)

namespace OrderIso

section LE

variable [LE α] [LE β] [LE γ] [LE δ]

/-- Identity order isomorphism. -/
def refl (α : Type*) [LE α] : α ≃o α :=
  RelIso.refl (· ≤ ·)

end LE
end OrderIso
end
