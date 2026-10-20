@[expose] public section

open scoped SetRel

variable {α : Type*} (r : SetRel α α)

variable {β : Type*} (s : SetRel β β)

namespace RelSeries

section

variable {r} {s : RelSeries r} {x : α}

lemma toList_getElem_zero_eq_head (p : RelSeries r) : p.toList[0] = p.head :=
  p.toList_getElem _

end
end RelSeries
end
