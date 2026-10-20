set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]

theorem openNormalCochainInflationCocone_jointly_surjective (n : ℕ)
    (σ : (TopRep.homogeneousCochains X).X n) :
    ∃ (U : OpenNormalSubgroup G) (τ : ((openNormalCochainDiagram X).obj U).X n),
      ((openNormalCochainInflationCocone X).ι.app U).f n τ = σ :=
  exists_openNormal_quotient_cochain_lift X n σ

end ContinuousCohomology
end
