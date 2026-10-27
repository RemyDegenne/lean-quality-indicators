@[expose] public section

open Metric Set unitInterval

open scoped Graph

namespace Schoenflies

namespace Plane

variable {u v w d z : Plane} {ρ : ℝ}

/-- The consecutive pairs of a finite set of directions, as a set. Indexing the sectors by this
set rather than by a chosen cyclic successor keeps the construction choice-free. -/
def sectorPairs (D : Set Plane) : Set (Plane × Plane) := {p | IsSectorPair D p.1 p.2}

end Plane
end Schoenflies
end
