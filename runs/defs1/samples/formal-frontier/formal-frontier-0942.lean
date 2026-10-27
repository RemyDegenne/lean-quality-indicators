@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set

namespace Topology.GenericPointRemoval

variable {X : Type u} [TopologicalSpace X]

/-- The complement of the selected generic points, with its induced topology. -/
abbrev Rest (G : Set X) := {x : X // x ∉ G}

end Topology.GenericPointRemoval
end
