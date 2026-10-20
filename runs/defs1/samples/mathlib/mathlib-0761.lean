@[expose] public section

universe u v

variable {α : Type u} {β : Type v}

namespace Multiplicative

/-- Reinterpret `x : Multiplicative α` as an element of `α`. -/
@[implicit_reducible]
def toAdd : Multiplicative α ≃ α := ofAdd.symm

end Multiplicative
end
