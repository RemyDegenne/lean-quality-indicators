@[expose] public section

open Function

namespace Set

section Prod

variable {α β γ δ : Type*} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

@[simp]
theorem prod_eq_iff_eq (ht : t.Nonempty) : s ×ˢ t = s₁ ×ˢ t ↔ s = s₁ := by
  simp_rw [prod_eq_prod_iff, ht.ne_empty, and_true, or_iff_left_iff_imp, or_false]
  rintro ⟨rfl, rfl⟩
  rfl

end Prod
end Set
end
