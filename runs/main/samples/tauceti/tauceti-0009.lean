public section

namespace TauCeti

open ContCohomology _root_.TauCeti.ContinuousCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {U : Subgroup G}

theorem cohomologicalDimensionAt_eq_of_isOpen_of_ne_top (hU : IsOpen (U : Set G))
    (hG : cohomologicalDimensionAt.{u} p G ≠ ⊤) :
    cohomologicalDimensionAt.{u} p U = cohomologicalDimensionAt.{u} p G :=
  le_antisymm (cohomologicalDimensionAt_le_of_isClosed (U.isClosed_of_isOpen hU))
    (cohomologicalDimensionAt_le_of_isOpen_of_ne_top hU hG)

end TauCeti
end
