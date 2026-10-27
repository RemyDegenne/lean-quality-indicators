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

/-- The canonical cocone whose legs inflate the classes of open-normal
quotients to continuous cohomology of the original representation. -/
noncomputable def openNormalInflationCocone : Cocone (openNormalCohomologyDiagram X n) where
  pt := continuousCohomology n X
  ι := {
    app M := map (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) n
    naturality := by
      intro M N f
      exact (quotientTransition_map_inflate X (leOfHom f) n).symm
  }

end ContinuousCohomology
end
