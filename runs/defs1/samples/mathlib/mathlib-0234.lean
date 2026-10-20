@[expose] public section

universe u

namespace Ordnode

variable {α : Type*}

local prefix:arg "ι" => Ordnode.singleton

section

variable [LE α] [DecidableLE α]

/-- O(m + n). Is every element of `t₁` equivalent to some element of `t₂`?

```
is_subset {1, 4} {1, 2, 4} = tt
is_subset {1, 3} {1, 2, 4} = ff
``` -/
def isSubset (t₁ t₂ : Ordnode α) : Bool :=
  decide (size t₁ ≤ size t₂) && isSubsetAux t₁ t₂

end
end Ordnode
end
