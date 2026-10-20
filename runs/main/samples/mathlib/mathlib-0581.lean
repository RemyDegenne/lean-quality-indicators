@[expose] public section

open OrderDual

universe u v

variable {α β : Type*}

export NoBotOrder (exists_not_ge)

export NoTopOrder (exists_not_le)

export NoMinOrder (exists_lt)

export NoMaxOrder (exists_gt)

section Preorder

variable [Preorder α] {a b : α}

@[to_dual]
theorem noMinOrder_iff : NoMinOrder α ↔ ∀ x : α, ¬ IsMin x := by
  simp [noMinOrder_iff', IsMin, lt_iff_le_not_ge]

end Preorder
end
