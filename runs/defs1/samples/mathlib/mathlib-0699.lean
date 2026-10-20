@[expose] public section

open OrderDual

universe u v

variable {α β : Type*}

/-- Order without bottom elements. -/
@[mk_iff noBotOrder_iff']
class NoBotOrder (α : Type*) [LE α] : Prop where
  /-- For each term `a`, there is some `b` which is either incomparable or strictly smaller. -/
  exists_not_ge (a : α) : ∃ b, ¬a ≤ b

end
