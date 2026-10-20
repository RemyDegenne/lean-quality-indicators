@[expose] public section

open Function

variable {α β : Type*} {a b c d e f : α}

section Semigroup

variable [Semigroup α]

section PartialOrder

variable [PartialOrder α]

/-- A semigroup with a partial order and satisfying `RightCancelSemigroup`
(i.e. `a * c < b * c → a < b`) is a `RightCancelSemigroup`. -/
@[to_additive (attr := instance_reducible)
/-- An additive semigroup with a partial order and satisfying `AddRightCancelSemigroup`
(`a + c < b + c → a < b`) is a `AddRightCancelSemigroup`. -/]
def Contravariant.toRightCancelSemigroup [MulRightReflectLE α] : RightCancelSemigroup α where

end PartialOrder
end Semigroup
end
