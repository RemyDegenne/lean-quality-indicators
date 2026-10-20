@[expose] public section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

namespace FreeMonoid

/-- Embeds an element of `α` into `FreeMonoid α` as a singleton list. -/
@[to_additive /-- Embeds an element of `α` into `FreeAddMonoid α` as a singleton list. -/]
def of (x : α) : FreeMonoid α := ofList [x]

end FreeMonoid
end
