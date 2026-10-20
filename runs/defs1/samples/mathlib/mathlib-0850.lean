@[expose] public section

variable {α : Type*}

local infixl:50 " ~ " => Lists.Equiv

namespace Lists

/-- Predicate stating that a ZFA list is proper. -/
def IsList (l : Lists α) : Prop :=
  l.1

end Lists
end
