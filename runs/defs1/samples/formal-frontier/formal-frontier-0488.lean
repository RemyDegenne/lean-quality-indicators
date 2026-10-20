@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set

namespace Topology.GenericPointRemoval

variable {X : Type u} [TopologicalSpace X]

/-- A strict specialization of `η`: a point outside the selected set to
which `η` specializes. -/
abbrev Strict (G : Set X) (η : G) := {σ : Rest G // η.1 ⤳ σ.1}

end Topology.GenericPointRemoval
end
