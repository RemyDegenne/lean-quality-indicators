public section

universe u v

namespace Set

variable {α : Type u} {β : Type v} {a b : α} {s : Set α}

section Preorder

variable [Preorder α] [Preorder β] {f : α → β}

theorem strictAntiOn_iff_strictAnti : StrictAntiOn f s ↔
    StrictAnti fun a : s => f a := by
  simp [StrictAnti, StrictAntiOn]

end Preorder
end Set
end
