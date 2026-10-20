@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*}

open Equiv Equiv.Perm Function

namespace Set

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ : α → β} {g g₁ g₂ : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β} {a : α} {b : β}

section bijOn

theorem BijOn.mapsTo (h : BijOn f s t) : MapsTo f s t :=
  h.left

end bijOn
end Set
end
