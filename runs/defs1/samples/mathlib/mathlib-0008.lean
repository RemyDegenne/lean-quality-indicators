@[expose] public section

universe u

namespace Ordnode

variable {α : Type*}

local prefix:arg "ι" => Ordnode.singleton

/-- O(n). Build a list of elements in descending order from the tree.

```
toRevList {1, 2, 4} = [4, 2, 1]
toRevList {2, 1, 1, 4} = [4, 2, 1]
``` -/
def toRevList (t : Ordnode α) : List α :=
  foldl (flip List.cons) [] t

end Ordnode
end
