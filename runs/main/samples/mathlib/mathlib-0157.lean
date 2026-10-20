@[expose] public section

open Function

namespace Set

section Prod

variable {α β γ δ : Type*} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

theorem prod_subset_prod_iff_left (h : t.Nonempty) : s ×ˢ t ⊆ s₁ ×ˢ t ↔ s ⊆ s₁ := by
  simp +contextual [prod_subset_prod_iff, or_iff_left h.ne_empty]

end Prod
end Set
end
