set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (X : TopRep.{max v w} k G)

variable {X} {Y Z : TopRep.{max v w} k G}

variable (X) (n : ℕ)

@[simp] theorem openNormalCohomologyDiagram_obj (M : OpenNormalSubgroup G) :
    (openNormalCohomologyDiagram X n).obj M =
      continuousCohomology n (TopRep.quotientInvariants M.toSubgroup X) := rfl

end ContinuousCohomology
end
