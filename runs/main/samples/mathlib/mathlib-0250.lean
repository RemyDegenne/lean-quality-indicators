@[expose] public section

open Function Set

variable {ι : Type*} {α : ι → Type*} {β : Type*}

variable {f : (Π i, α i) → β}

lemma DependsOn.mono {s t : Set ι} (hst : s ⊆ t) (hf : DependsOn f s) : DependsOn f t :=
  fun _ _ h ↦ hf fun i hi ↦ h i (hst hi)

end
