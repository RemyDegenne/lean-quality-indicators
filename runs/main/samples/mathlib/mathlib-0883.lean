@[expose] public section

open List (Vector)

open Function Order Set

noncomputable section

universe u v w v' w'

variable {α β : Type u}

namespace Cardinal

theorem mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ s) :
    #(insert a s : Set α) = #s + 1 := by
  rw [← union_singleton, mk_union_of_disjoint, mk_singleton]
  simpa

end Cardinal
end
end
