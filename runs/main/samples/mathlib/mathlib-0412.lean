@[expose] public section

open Function

variable {F α β γ δ : Type*}

infixr:25 " →+o " => OrderAddMonoidHom

infixr:25 " ≃+o " => OrderAddMonoidIso

infixr:25 " →*o " => OrderMonoidHom

infixr:25 " ≃*o " => OrderMonoidIso

namespace OrderMonoidHom

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

variable (α)

variable {α}

@[to_additive (attr := simp)]
theorem comp_one (f : β →*o γ) : f.comp (1 : α →*o β) = 1 :=
  ext fun _ => map_one f

end Preorder
end OrderMonoidHom
end
