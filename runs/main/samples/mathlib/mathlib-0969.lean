@[expose] public section

open Function

variable {α β : Type*} {a b c d e f : α}

section MulOneClass

variable [MulOneClass α]

section LE

variable [LE α]

@[to_additive add_le_of_nonpos_left]
theorem mul_le_of_le_one_left' [MulRightMono α] (h : b ≤ 1) : b * a ≤ a := by
  simpa using mul_le_mul_left h a

end LE
end MulOneClass
end
