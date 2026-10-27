@[expose] public section

open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

@[inherit_doc]
infixl:25 " ≃ " => Equiv

namespace Equiv

section

/-- A `PSigma`-type is equivalent to the corresponding `Sigma`-type. -/
@[simps (attr := grind =) apply symm_apply]
def psigmaEquivSigma {α} (β : α → Type*) : (Σ' i, β i) ≃ Σ i, β i where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

end
end Equiv
end
