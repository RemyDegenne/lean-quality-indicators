@[expose] public section

open Set Bornology Filter

open scoped Pointwise

section Defs

variable (M : Type*) {α : Type*} [Bornology M] [SMul M α]

/-- A set is *absorbent* if it absorbs every singleton. -/
def Absorbent (s : Set α) : Prop :=
  ∀ x, Absorbs M s {x}

end Defs
end
