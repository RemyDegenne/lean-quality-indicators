@[expose] public section

open Function

variable {α β : Type*} {a b c d e f : α}

section MulOneClass

variable [MulOneClass α]

section LE

variable [LE α]

@[to_additive add_le_of_nonpos_right]
theorem mul_le_of_le_one_right' [MulLeftMono α] (h : b ≤ 1) : a * b ≤ a := by
  simpa using mul_le_mul_right h a

end LE
end MulOneClass
end
