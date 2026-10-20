@[expose] public section

universe u v l

namespace FreeSemigroup

variable {α : Type u}

/-- Length of an element of free semigroup. -/
@[to_additive /-- Length of an element of free additive semigroup -/]
def length (x : FreeSemigroup α) : ℕ := x.tail.length + 1

end FreeSemigroup
end
