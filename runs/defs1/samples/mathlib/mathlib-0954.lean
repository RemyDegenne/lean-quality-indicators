@[expose] public section

variable {α : Sort*} {β : Sort*}

@[inherit_doc Quotient.mk]
notation3:arg "⟦" a "⟧" => Quotient.mk _ a

namespace Quotient

variable {γ : Sort*} {φ : Sort*} {s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}

/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements
to a function `f : Quotient sa → Quotient sb → Quotient sc`. Useful to define binary operations
on quotients. This is a version of `Quotient.map₂` using `Setoid.r` instead of `≈`. -/
protected def map₂' (f : α → β → γ)
    (h : ∀ ⦃a₁ a₂ : α⦄, s₁.r a₁ a₂ → ∀ ⦃b₁ b₂ : β⦄, s₂.r b₁ b₂ → s₃.r (f a₁ b₁) (f a₂ b₂)) :
    Quotient s₁ → Quotient s₂ → Quotient s₃ :=
  Quotient.map₂ f h

end Quotient
end
