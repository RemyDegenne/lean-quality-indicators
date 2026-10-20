@[expose] public section

open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {F : Set β} {W P D : List β}

namespace Graph

theorem IsWalk.of_deleteEdges (h : (G.deleteEdges F).IsWalk u W v) : G.IsWalk u W v :=
  h.mono deleteEdges_le

end Graph
end
