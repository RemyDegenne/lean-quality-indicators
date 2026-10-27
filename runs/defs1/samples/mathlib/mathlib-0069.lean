@[expose] public section

variable {α : Type*}

section LinearOrder

macro "compareOfLessAndEq_rfl" : tactic =>
  `(tactic| (intro a b; first | rfl |
    (simp only [compare, compareOfLessAndEq]; split_ifs <;> rfl) |
    (induction a <;> induction b <;> simp +decide only)))

variable [LinearOrder α] {a b c : α}

attribute [instance_reducible, instance 900] LinearOrder.toDecidableLT

attribute [instance_reducible, instance 900] LinearOrder.toDecidableLE

attribute [instance_reducible, instance 900] LinearOrder.toDecidableEq

/-- The category of linear orders.

This will get reused to define `OrderType`. -/
structure LinOrd where
  /-- Construct a bundled `LinOrd` from the underlying type and typeclass. -/
  of ::
  /-- The underlying linearly ordered type. -/
  (carrier : Type*)
  [str : LinearOrder carrier]

end LinearOrder
end
