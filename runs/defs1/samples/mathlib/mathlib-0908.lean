@[expose] public section

open Function

universe u

variable {α α₁ α₂ β β₁ β₂ γ δ : Sort*}

namespace Equiv

section

/-- `PEmpty` type is a left absorbing element for type product up to an equivalence. -/
def pemptyProd (α) : PEmpty × α ≃ PEmpty :=
  equivPEmpty _

end
end Equiv
end
