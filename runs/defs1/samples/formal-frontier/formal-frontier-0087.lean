@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality.FiniteCoordinates

variable {X : Type u} [TopologicalSpace X]

/-- Compatible choices of a realized pattern at every finite coordinate stage. -/
def Family (X : Type u) [TopologicalSpace X] : Type u :=
  {z : ∀ F : Finset (CompactOpens X), Stage F //
    ∀ (F G : Finset (CompactOpens X)) (hFG : F ⊆ G),
      restrict (X := X) hFG (z G) = z F}

end SpectralStoneDuality.FiniteCoordinates
end
