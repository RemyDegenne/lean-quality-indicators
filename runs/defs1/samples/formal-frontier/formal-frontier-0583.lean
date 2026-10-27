@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality.FiniteCoordinates

variable {X : Type u} [TopologicalSpace X]

/-- Membership in a finite compact-open coordinate of a stage. -/
def coordinateOpen (F : Finset (CompactOpens X)) (U : Coordinates F) : Opens (Stage F) :=
  ⟨{v | v.1 U}, continuous_Prop.mp
    ((continuous_apply U).comp continuous_subtype_val)⟩

end SpectralStoneDuality.FiniteCoordinates
end
