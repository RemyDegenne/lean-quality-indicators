public section

universe u v

variable {α : Type u} {β : Type v}

section

variable [LinearOrder α] [LinearOrder β] {f : α → β} {s : Set α} {a b c d : α}

@[to_dual]
theorem max_left_commutative : LeftCommutative (max : α → α → α) := ⟨max_left_comm⟩

end
end
