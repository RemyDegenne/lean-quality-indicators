@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set

namespace Topology.GenericPointRemoval

variable {X : Type u} [TopologicalSpace X]

variable (G : Set X)

/-- Define the underlying gluing function by its values on the selected
generic points and on their complement. -/
noncomputable def extend {W : Type v} (h : Forks G → W) (q : Rest G → W) : X → W := by
  classical
  exact fun x => if hx : x ∈ G then h ⟨⟨x, hx⟩, .generic⟩ else q ⟨x, hx⟩

end Topology.GenericPointRemoval
end
