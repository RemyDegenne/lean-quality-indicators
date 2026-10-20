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
theorem cancel_right {g₁ g₂ : β →Co γ} {f : α →Co β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

end Preorder
end ContinuousOrderHom
end
end
