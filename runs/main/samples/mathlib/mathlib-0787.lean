public section

variable {α α' α'' β : Type*} {G H : Graph α β} {f g : α → α'} {u v : α} {e : β} {x y : α'}

open Set Relation

namespace Graph

section Map

@[simp]
lemma map_adj (f : α → α') : (G.map f).Adj x y ↔ Relation.Map G.Adj f f x y := by
  simp only [Adj, map_isLink, map_apply]
  tauto

end Map
end Graph
end
