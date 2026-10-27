@[expose] public section

universe u v w

open List

variable {α : Type u} {β : α → Type v}

local notation:arg "⟦" a "⟧" => AList.toFinmap a

namespace Finmap

open AList

section

variable [DecidableEq α]

/-- Look up the value associated to a key in a map. -/
def lookup (a : α) (s : Finmap β) : Option (β a) :=
  liftOn s (AList.lookup a) fun _ _ => perm_lookup

end
end Finmap
end
