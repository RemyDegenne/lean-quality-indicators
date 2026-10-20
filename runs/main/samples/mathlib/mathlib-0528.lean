@[expose] public section

open Function

variable {α β : Type*} {a b c d e f : α}

section Mul

variable [Mul α]

section Preorder

variable [Preorder α]

@[to_additive]
lemma mul_right_strictMono [MulLeftStrictMono α] : StrictMono (a * ·) :=
  fun _ _ h ↦ mul_lt_mul_right h _

end Preorder
end Mul
end
