@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*}

namespace SetRel

variable {R R₁ R₂ : SetRel α β} {S : SetRel β γ} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {u : Set γ}
  {a a₁ a₂ : α} {b : β} {c : γ}

scoped notation:50 a:50 " ~[" R "] " b:50 => (a, b) ∈ R

@[inherit_doc] scoped infixl:62 " ○ " => comp

@[gcongr] lemma image_subset_image_left (hR : R₁ ⊆ R₂) : image R₁ s ⊆ image R₂ s :=
  fun _ ⟨a, ha, hab⟩ ↦ ⟨a, ha, hR hab⟩

end SetRel
end
