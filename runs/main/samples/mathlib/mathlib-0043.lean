@[expose] public section

open Function

variable {α β : Type*} {ι κ : Sort*} (r r' s : α → α → Prop)

local infixl:50 " ≼ " => r

variable {r r'}

theorem directed_comp {ι} {f : ι → β} {g : β → α} : Directed r (g ∘ f) ↔ Directed (g ⁻¹'o r) f :=
  Iff.rfl

end
