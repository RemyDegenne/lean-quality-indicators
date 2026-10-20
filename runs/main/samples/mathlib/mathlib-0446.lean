@[expose] public section

open Function Set

variable {α β γ ι ι' : Type*} {r p : α → α → Prop}

namespace Set

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {s t : Set ι} {f g : ι → α}

theorem PairwiseDisjoint.image_of_le (hs : s.PairwiseDisjoint f) {g : ι → ι} (hg : f ∘ g ≤ f) :
    (g '' s).PairwiseDisjoint f := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
  exact (hs ha hb <| ne_of_apply_ne _ h).mono (hg a) (hg b)

end PartialOrderBot
end Set
end
