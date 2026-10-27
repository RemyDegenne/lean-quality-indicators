@[expose] public section

open Set

open scoped Pointwise

namespace MulAction

section SMul

variable (G : Type*) {X : Type*} [SMul G X] {B : Set X} {a : X}

/-- A set `B` is a `G`-block iff the sets of the form `g • B` are pairwise equal or disjoint. -/
@[to_additive
/-- A set `B` is a `G`-block iff the sets of the form `g +ᵥ B` are pairwise equal or disjoint. -/]
def IsBlock (B : Set X) := ∀ ⦃g₁ g₂ : G⦄, g₁ • B ≠ g₂ • B → Disjoint (g₁ • B) (g₂ • B)

end SMul
end MulAction
end
