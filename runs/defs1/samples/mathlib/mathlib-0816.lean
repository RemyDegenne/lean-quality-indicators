@[expose] public section

universe u

namespace Ordnode

variable {α : Type*}

local prefix:arg "ι" => Ordnode.singleton

section

variable [LE α] [DecidableLE α]

/-- Auxiliary definition for `findIndex`. -/
def findIndexAux (x : α) : Ordnode α → ℕ → Option ℕ
  | nil, _ => none
  | node _ l y r, i =>
    match cmpLE x y with
    | Ordering.lt => findIndexAux x l i
    | Ordering.eq => some (i + size l)
    | Ordering.gt => findIndexAux x r (i + size l + 1)

end
end Ordnode
end
