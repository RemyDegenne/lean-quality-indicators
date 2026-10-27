@[expose] public section

namespace AgreeToDisagree

open Set

variable {α Ω : Type*}

section Prerequisites

/-- We write `Partition α` for the type of partitions of a set `α`, implemented as a subtype
of `Set (Set α)`. Mathlib already equips this subtype with the order given by refinement (such that
`P ≤ Q` iff `P` refines `Q`) and proves that it is a complete lattice, i.e. that arbitrary infima
and suprema of partitions exist. -/
abbrev Partition (α : Type*) := Setoid.Partitions α

end Prerequisites
end AgreeToDisagree
end
