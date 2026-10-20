@[expose] public section

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*}

namespace Finset

attribute [local trans] Subset.trans Superset.trans

section Sdiff

variable [DecidableEq α] {s t : Finset α} {a b : α}

theorem sdiff_insert (s t : Finset α) (x : α) : s \ insert x t = (s \ t).erase x := by
  grind

end Sdiff
end Finset
end
