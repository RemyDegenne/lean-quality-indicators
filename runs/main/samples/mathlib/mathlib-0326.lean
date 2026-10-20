@[expose] public section

open Function Set

open scoped Pointwise

variable {α : Type*}

namespace QuotientGroup

variable [Group α] {s : Subgroup α}

@[to_additive]
theorem out_eq' (a : α ⧸ s) : mk a.out = a :=
  Quotient.out_eq' a

end QuotientGroup
end
