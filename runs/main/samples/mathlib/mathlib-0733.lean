@[expose] public section

open Function

universe u v

namespace Set

variable {α : Type u} {β : Type v} {a b : α} {s s₁ s₂ t t₁ t₂ u : Set α}

theorem inter_nonempty_iff_exists_right : (s ∩ t).Nonempty ↔ ∃ x ∈ t, x ∈ s := by
  simp_rw [inter_nonempty, and_comm]

end Set
end
