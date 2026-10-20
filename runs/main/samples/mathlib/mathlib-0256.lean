@[expose] public section

open Function OrderDual

variable {F α β γ δ : Type*}

export TopHomClass (map_top)

export BotHomClass (map_bot)

variable [FunLike F α β]

namespace BoundedOrderHom

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [BoundedOrder α] [BoundedOrder β]
  [BoundedOrder γ] [BoundedOrder δ]

variable (α)

variable {α}

@[simp]
theorem id_comp (f : BoundedOrderHom α β) : (BoundedOrderHom.id β).comp f = f :=
  BoundedOrderHom.ext fun _ => rfl

end BoundedOrderHom
end
