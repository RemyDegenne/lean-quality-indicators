@[expose] public section

open Function Set

open OrderDual (toDual ofDual)

variable {α β γ : Type*} {ι : Sort*}

macro "bddDefault" : tactic =>
  `(tactic| first
    | apply OrderTop.bddAbove
    | apply OrderBot.bddBelow)

section PartialOrder

variable [PartialOrder α] {s : Set α} {a b : α}

@[to_dual self (reorder := a b, Ha Hb)]
theorem Set.subsingleton_of_isLUB_le_isGLB (Ha : IsGLB s a) (Hb : IsLUB s b) (hab : b ≤ a) :
    s.Subsingleton := fun _ hx _ hy =>
  le_antisymm (le_of_isLUB_le_isGLB Ha Hb hab hx hy) (le_of_isLUB_le_isGLB Ha Hb hab hy hx)

end PartialOrder
end
