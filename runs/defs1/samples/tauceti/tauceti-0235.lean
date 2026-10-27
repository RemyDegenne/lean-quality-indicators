public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

namespace Walk

variable {x y z w : α}

/-- Auxiliary tail-recursive operation used to reverse a walk. -/
protected def reverseAux {x y z : α} : G.Walk x y → G.Walk x z → G.Walk y z
  | .nil, q => q
  | .cons e h p, q => p.reverseAux (.cons e h.symm q)

end Walk
end Graph
end
