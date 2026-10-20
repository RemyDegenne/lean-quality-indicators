@[expose] public section

open Function

universe u v

namespace Set

variable {α : Type u} {β : Type v} {a b : α} {s s₁ s₂ t t₁ t₂ u : Set α}

theorem nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).Nonempty :=
  nonempty_of_not_subset ht.2

end Set
end
