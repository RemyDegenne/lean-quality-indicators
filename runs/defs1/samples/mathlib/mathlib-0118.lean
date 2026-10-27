@[expose] public section

namespace LinearGrowth

open EReal Filter Function

open scoped Topology

section definition

variable {R : Type*} [ConditionallyCompleteLattice R] [Div R] [NatCast R]

/-- Upper linear growth of a sequence. -/
noncomputable def linearGrowthSup (u : ℕ → R) : R := limsup (fun n ↦ u n / n) atTop

end definition
end LinearGrowth
end
