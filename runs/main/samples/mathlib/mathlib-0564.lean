@[expose] public section

noncomputable section

open Order Set

universe u

namespace Ordinal

variable {f : Ordinal.{u} → Ordinal.{u}} {o o₁ o₂ a b x : Ordinal.{u}}

@[inherit_doc] scoped notation "ε_ " => epsilon

scoped notation "ε₀" => ε_ 0

@[inherit_doc] scoped notation "Γ_ " => gamma

scoped notation "Γ₀" => Γ_ 0

section Countable

open Cardinal

@[simp]
theorem card_epsilon (o : Ordinal) : (ε_ o).card = max ℵ₀ o.card := by
  rw [card_veblen_of_left_ne_zero o one_ne_zero,
    card_one, max_right_comm, max_eq_right one_le_aleph0]

end Countable
end Ordinal
end
end
