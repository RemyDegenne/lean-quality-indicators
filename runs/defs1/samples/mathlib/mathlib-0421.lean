@[expose] public section

open Lean Elab Term Meta Batteries.ExtendedBinder

universe u

variable {α : Type u}

namespace Set

/-- The subset relation on sets. `s ⊆ t` means that all elements of `s` are elements of `t`.

Note that you should **not** use this definition directly, but instead write `s ⊆ t`. -/
protected def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

end Set
end
