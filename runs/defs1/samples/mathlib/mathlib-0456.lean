@[expose] public section

open Function

universe u v w

variable {α β γ δ : Type*} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop} {u : δ → δ → Prop}

infixl:25 " →r " => RelHom

infixl:25 " ↪r " => RelEmbedding

infixl:25 " ≃r " => RelIso

namespace RelIso

/-- A relation isomorphism between equal relations on equal types. -/
@[simps! toEquiv apply]
protected def cast {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} (h₁ : α = β)
    (h₂ : r ≍ s) : r ≃r s :=
  ⟨Equiv.cast h₁, @fun a b => by
    subst h₁
    rw [eq_of_heq h₂]
    rfl⟩

end RelIso
end
