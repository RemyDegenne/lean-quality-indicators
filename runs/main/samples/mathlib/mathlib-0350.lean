@[expose] public section

variable {α β : Type*} {s : α → Set β}

namespace Set

theorem accumulate_def [LE α] {x : α} : accumulate s x = ⋃ y ≤ x, s y :=
  rfl

end Set
end
