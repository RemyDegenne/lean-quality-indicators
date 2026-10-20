@[expose] public section

open Function OrderDual

variable {α β : Type*}

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

section PositivityExt

variable {α : Type*} [GroupWithZero α] [PartialOrder α]

variable {a b : α}

lemma zpow_zero_pos {α : Type*} [Semifield α] [PartialOrder α] [IsStrictOrderedRing α]
    (a : α) : 0 < a ^ (0 : ℤ) :=
  zero_lt_one.trans_eq (zpow_zero a).symm

end PositivityExt
end Mathlib.Meta.Positivity
end
