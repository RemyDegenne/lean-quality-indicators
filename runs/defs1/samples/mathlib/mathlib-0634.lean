@[expose] public section

open Function

universe u

variable {α α₁ α₂ β β₁ β₂ γ δ : Sort*}

namespace Equiv

section

/-- The type of functions to a product `β × γ` is equivalent to the type of pairs of functions
`α → β` and `β → γ`. -/
@[simps]
def arrowProdEquivProdArrow (α : Type*) (β γ : α → Type*) :
    ((i : α) → β i × γ i) ≃ ((i : α) → β i) × ((i : α) → γ i) where
  toFun := fun f => (fun c => (f c).1, fun c => (f c).2)
  invFun := fun p c => (p.1 c, p.2 c)

end
end Equiv
end
