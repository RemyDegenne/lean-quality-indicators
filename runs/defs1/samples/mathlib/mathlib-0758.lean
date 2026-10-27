@[expose] public section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

namespace FreeMonoid

/-- The identity equivalence between `List α` and `FreeMonoid α`. -/
@[to_additive /-- The identity equivalence between `List α` and `FreeAddMonoid α`. -/]
def ofList : List α ≃ FreeMonoid α := Equiv.refl _

end FreeMonoid
end
