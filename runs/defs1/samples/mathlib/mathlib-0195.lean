@[expose] public section

universe u

namespace Ordnode

variable {α : Type*}

local prefix:arg "ι" => Ordnode.singleton

/-- O(log n). Extract and remove the minimum element from the tree, if it exists.

```
split_min {1, 2, 3} = some (1, {2, 3})
split_min ∅ = none
``` -/
def splitMin : Ordnode α → Option (α × Ordnode α)
  | nil => none
  | node _ l x r => splitMin' l x r

end Ordnode
end
