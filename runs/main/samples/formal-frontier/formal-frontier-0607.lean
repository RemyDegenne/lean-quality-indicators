set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (X : TopRep.{max v w} k G)

theorem openNormalCochainDiagram_map_f_injective
    {U V : OrderDual (OpenNormalSubgroup G)} (f : U ⟶ V) (n : ℕ) :
    Function.Injective (((openNormalCochainDiagram X).map f).f n) :=
  cochainsMap_injective _ _ (quotientTransitionHom_surjective V U (leOfHom f))
    (quotientTransitionIncl_injective X (leOfHom f)) n

end ContinuousCohomology
end
