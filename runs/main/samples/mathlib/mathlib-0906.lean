@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*}

open Equiv Equiv.Perm Function

namespace Set

section equality

variable {s s₁ s₂ : Set α} {f₁ f₂ f₃ : α → β} {g : β → γ} {a : α}

theorem EqOn.comp_left (h : s.EqOn f₁ f₂) : s.EqOn (g ∘ f₁) (g ∘ f₂) := fun _ ha =>
  congr_arg _ <| h ha

end equality
end Set
end
