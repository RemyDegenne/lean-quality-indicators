@[expose] public section

open Function

variable {F α β γ δ : Type*}

@[inherit_doc] infixr:25 " →Co " => ContinuousOrderHom

section

namespace ContinuousOrderHom

variable [TopologicalSpace α] [Preorder α] [TopologicalSpace β]

section Preorder

variable [Preorder β] [TopologicalSpace γ] [Preorder γ] [TopologicalSpace δ] [Preorder δ]

variable (α)

variable {α}

@[simp]
theorem cancel_left {g : β →Co γ} {f₁ f₂ : α →Co β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Preorder
end ContinuousOrderHom
end
end
