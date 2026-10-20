@[expose] public section

namespace Matrix

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

section KroneckerMap

theorem kroneckerMap_add_left [Add α] [Add γ] (f : α → β → γ)
    (hf : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b) (A₁ A₂ : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (A₁ + A₂) B = kroneckerMap f A₁ B + kroneckerMap f A₂ B :=
  ext fun _ _ => hf _ _ _

end KroneckerMap
end Matrix
end
