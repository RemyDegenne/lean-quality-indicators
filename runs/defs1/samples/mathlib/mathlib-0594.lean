@[expose] public section

open scoped SetRel

variable {α : Type*} (r : SetRel α α)

variable {β : Type*} (s : SetRel β β)

namespace RelSeries

section

variable {r} {s : RelSeries r} {x : α}

/-- End of a series, i.e. for `a₀ -r→ a₁ -r→ ... -r→ aₙ`, its last element is `aₙ`.

Since a relation series is assumed to be non-empty, this is well defined. -/
def last (x : RelSeries r) : α := x <| Fin.last _

end
end RelSeries
end
