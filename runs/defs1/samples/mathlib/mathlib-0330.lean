@[expose] public section

open Relation

open scoped List

universe u v w

variable {α : Type u}

attribute [local simp] List.append_eq_has_append

namespace FreeGroup

variable {L L₁ L₂ L₃ : List (α × Bool)}

/-- The bijection between the free group on a unique type and the integers. -/
def equivIntOfUnique [Unique α] : FreeGroup α ≃ ℤ where
  toFun x := sum (map 1 x)
  invFun x := of default ^ x
  left_inv x := by
    induction x with
    | one => simp
    | of x => simp [Unique.default_eq x]
    | inv_of x hx => simp [Unique.default_eq x]
    | mul x y hx hy => simp [zpow_add, hx, hy]
  right_inv x := by
    induction x with
    | zero => simp
    | succ x hx => simpa [zpow_add_one] using hx
    | pred x hx => simpa [zpow_sub_one, ← sub_eq_add_neg] using hx

end FreeGroup
end
