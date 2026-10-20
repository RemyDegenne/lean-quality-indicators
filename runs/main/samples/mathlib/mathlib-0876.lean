public section

universe u v

open Function Set

namespace Set

variable {α β γ : Type*} {ι : Sort*}

section Range

variable {f : ι → α} {s t : Set α}

@[simp]
theorem _root_.Prod.range_snd [Nonempty α] : range (Prod.snd : α × β → β) = univ :=
  Prod.snd_surjective.range_eq

end Range
end Set
end
