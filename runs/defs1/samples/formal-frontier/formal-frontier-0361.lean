@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality.FiniteCoordinates

variable {X : Type u} [TopologicalSpace X]

/-- The value of a compatible family at one compact open. -/
def coordinateValue (z : Family X) (U : CompactOpens X) : Prop :=
  (z.1 {U}).1 ⟨U, Finset.mem_singleton_self U⟩

end SpectralStoneDuality.FiniteCoordinates
end
