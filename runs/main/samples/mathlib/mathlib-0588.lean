@[expose] public section

noncomputable section

variable {α β : Type*}

namespace Finite

theorem card_eq_zero_iff [Finite α] : Nat.card α = 0 ↔ IsEmpty α := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]

end Finite
end
end
