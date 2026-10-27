@[expose] public section

open Bornology Set

variable {α : Type*} {s t : Set α}

variable [Bornology α]

variable (α) [Preorder α] in
/-- Predicate for a preorder to be equipped with its order-bornology, namely for its bounded sets
to be the ones that are bounded both above and below. -/
class IsOrderBornology : Prop where
  protected isBounded_iff_bddBelow_bddAbove (s : Set α) : IsBounded s ↔ BddBelow s ∧ BddAbove s

end
