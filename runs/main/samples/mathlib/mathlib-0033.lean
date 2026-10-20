@[expose] public section

open Function

variable {α β : Type*} {a b c d e f : α}

section MulOneClass

variable [MulOneClass α]

section LT

variable [LT α]

@[to_additive (attr := simp) add_lt_iff_neg_left]
theorem mul_lt_iff_lt_one_left' [MulLeftStrictMono α] [MulLeftReflectLT α] (a : α) :
    a * b < a ↔ b < 1 := by
  simpa using mul_lt_mul_iff_left a (c := 1)

end LT
end MulOneClass
end
