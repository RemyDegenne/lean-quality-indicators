public section

variable {α : Type*}

section OrderedAddCommSemigroup

section Preorder

variable [Preorder α]

section AddCommSemigroup

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

section Cov

variable [AddLeftMono α]

theorem add_tsub_add_le_tsub_right : a + c - (b + c) ≤ a - b := by
  grw [tsub_le_iff_left, add_right_comm, ← le_add_tsub]

end Cov
end AddCommSemigroup
end Preorder
end OrderedAddCommSemigroup
end
