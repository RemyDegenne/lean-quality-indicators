@[expose] public section

open Function Set

universe u v w w'

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort w'}

open Order

namespace CompleteDistribLattice

variable [CompleteLattice α] (minAx : MinimalAxioms α)

/-- Construct a complete distrib lattice instance using the minimal amount of work needed.

This sets `a ⇨ b := sSup {c | c ⊓ a ≤ b}`, `aᶜ := a ⇨ ⊥`, `a \ b := sInf {c | a ≤ b ⊔ c}` and
`￢a := ⊤ \ a`. -/
-- See note [reducible non-instances]
abbrev ofMinimalAxioms [CompleteLattice α] (minAx : MinimalAxioms α) :
    CompleteDistribLattice α where
  __ := Frame.ofMinimalAxioms minAx.toFrame
  __ := Coframe.ofMinimalAxioms minAx.toCoframe

end CompleteDistribLattice
end
