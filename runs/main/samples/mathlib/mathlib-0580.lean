@[expose] public section

open Function

universe u v w x

namespace Function

section

variable {α β γ : Sort*} {f : α → β}

@[simp]
theorem Surjective.of_comp_iff' (hf : Bijective f) (g : γ → α) :
    Surjective (f ∘ g) ↔ Surjective g :=
  ⟨fun S ↦ S.of_comp_left hf.1, hf.surjective.comp⟩

end
end Function
end
