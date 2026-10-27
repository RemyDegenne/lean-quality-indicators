@[expose] public section

universe u v w

variable {α : Type u} {β : Type v}

open OrderDual

section lift

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `SemilatticeInf` across an `Equiv`. -/
protected abbrev semilatticeInf [SemilatticeInf β] : SemilatticeInf α := by
  let min := e.min
  let partialOrder := e.partialOrder
  apply e.injective.semilatticeInf <;> intros <;> first | rfl | exact e.apply_symm_apply _

end Equiv
end lift
end
