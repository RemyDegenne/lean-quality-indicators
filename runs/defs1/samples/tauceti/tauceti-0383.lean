universe u

public section

open Topology

namespace TauCeti

variable {F : Type*} [TopologicalSpace F]

/-- A mapping-torus presentation of a topological space, including its fibre and monodromy. -/
structure MappingTorusPresentation (M : Type u) [TopologicalSpace M] where
  /-- The fibre type. -/
  Fiber : Type u
  /-- The fibre is nonempty. -/
  nonemptyFiber : Nonempty Fiber
  /-- The topology carried by the fibre. -/
  fiberTopology : TopologicalSpace Fiber
  /-- The monodromy homeomorphism around the circle. -/
  monodromy : @Homeomorph Fiber Fiber fiberTopology fiberTopology
  /-- A homeomorphism from the presented space to the mapping torus. -/
  equivalence : @Homeomorph M (@MappingTorus Fiber fiberTopology monodromy)
      (by infer_instance) instTopologicalSpaceQuotient

end TauCeti
end
