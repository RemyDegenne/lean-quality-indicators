public section

variable {ι ι' α β : Type*}

open Set

namespace Filter

section IsDirected

variable [Nonempty α] [Preorder α] [IsDirectedOrder α] {f : α → β} {l : Filter β}

variable [Preorder β]

@[to_dual]
theorem tendsto_atTop_atBot_iff_of_antitone (hf : Antitone f) :
    Tendsto f atTop atBot ↔ ∀ b : β, ∃ a, f a ≤ b :=
  tendsto_atTop_atTop_iff_of_monotone (β := βᵒᵈ) hf

end IsDirected
end Filter
end
