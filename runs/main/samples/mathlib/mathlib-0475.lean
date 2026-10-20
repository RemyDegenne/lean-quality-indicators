@[expose] public section

namespace Set

variable {α β : Type*} {s t : Set α}

section ncard

syntax "toFinite_tac" : tactic

macro_rules
  | `(tactic| toFinite_tac) => `(tactic| apply Set.toFinite)

syntax "to_encard_tac" : tactic

macro_rules
  | `(tactic| to_encard_tac) => `(tactic|
      simp only [← Nat.cast_le (α := ℕ∞), ← Nat.cast_inj (R := ℕ∞), Nat.cast_add, Nat.cast_one])

variable {f : α → β}

theorem ncard_strictMono [Finite α] : @StrictMono (Set α) _ _ _ ncard :=
  fun _ _ h ↦ ncard_lt_ncard h

end ncard
end Set
end
