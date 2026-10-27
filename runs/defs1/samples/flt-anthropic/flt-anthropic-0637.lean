set_option autoImplicit false

open MeasureTheory Filter Topology

namespace TestFunctionAction

section Check

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def checkHomeomorph (σ : G ≃ₜ* G) : G ≃ₜ G :=
  (Homeomorph.inv G).trans σ.symm.toHomeomorph

end Check
end TestFunctionAction
