@[expose] public section

open Function

section Quantifiers

variable {α β : Sort*} {p : α → Prop}

export Classical (not_forall)

export Classical (not_exists_not)

theorem forall_or_of_or_forall {α : Sort*} {p : α → Prop} {b : Prop} (h : b ∨ ∀ x, p x) (x : α) :
    b ∨ p x :=
  h.imp_right fun h₂ ↦ h₂ x

end Quantifiers
end
