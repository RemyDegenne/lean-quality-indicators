@[expose] public section

universe u v

variable {ι : Sort*} {α β γ δ : Type*}

open OmegaCompletePartialOrder Chain

namespace OmegaCompletePartialOrder

variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

variable [OmegaCompletePartialOrder γ] [OmegaCompletePartialOrder δ]

@[inherit_doc] infixr:25 " →𝒄 " => ContinuousHom

namespace ContinuousHom

theorem ωSup_apply_ωSup (c₀ : Chain (α →𝒄 β)) (c₁ : Chain α) :
    ωSup c₀ (ωSup c₁) = Prod.apply (ωSup (c₀.zip c₁)) := by simp [Prod.apply_apply, Prod.ωSup_zip]

end ContinuousHom
end OmegaCompletePartialOrder
end
