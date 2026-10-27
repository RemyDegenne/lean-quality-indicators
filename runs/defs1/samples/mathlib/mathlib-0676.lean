@[expose] public section

variable {α : Type*} (p : α → Prop) [DecidablePred p]

namespace FreeAddMonoid

/-- `List.countP` as a bundled additive monoid homomorphism. -/
def countP : FreeAddMonoid α →+ ℕ where
  toFun := FreeAddMonoid.countP' p
  map_zero' := countP'_zero p
  map_add' := countP'_add p

end FreeAddMonoid
end
