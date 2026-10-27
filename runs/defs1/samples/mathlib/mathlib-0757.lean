@[expose] public section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

namespace FreeMonoid

section Length

variable {a : FreeMonoid α}

/-- The length of a free monoid element: 1.length = 0 and (a * b).length = a.length + b.length -/
@[to_additive /-- The length of an additive free monoid element: 1.length = 0 and (a + b).length =
  a.length + b.length -/]
def length (a : FreeMonoid α) : ℕ := a.toList.length

end Length
end FreeMonoid
end
