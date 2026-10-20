@[expose] public section

variable {α β γ : Type*}

open Multiset

open Function

namespace Finset

section Map

variable {f : α ↪ β} {s : Finset α}

@[simp]
theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ := (map_injective f).eq_iff' (map_empty f)

end Map
end Finset
end
