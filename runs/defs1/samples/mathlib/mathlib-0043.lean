@[expose] public section

open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

@[inherit_doc]
infixl:25 " ≃ " => Equiv

namespace Equiv

section

/-- A `Sigma` with `fun i ↦ ULift (PLift (P i))` fibers is equivalent to `{ x // P x }`.
Variant of `sigmaPLiftEquivSubtype`.
-/
def sigmaULiftPLiftEquivSubtype {α : Type v} (P : α → Prop) :
    (Σ i, ULift (PLift (P i))) ≃ Subtype P :=
  (sigmaCongrRight fun _ => Equiv.ulift).trans (sigmaPLiftEquivSubtype P)

end
end Equiv
end
