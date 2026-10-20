set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (X : TopRep.{max v w} k G)

/-- Homogeneous cochains on open-normal quotients, directed by refinement.
An arrow `U ⟶ V` means `V ≤ U`: the group map is `G/V → G/U`, and the
coefficient map includes `U`-invariants into `V`-invariants. -/
def openNormalCochainDiagram :
    OrderDual (OpenNormalSubgroup G) ⥤
      CochainComplex (TopModuleCat.{max v w} k) ℕ where
  obj U := TopRep.homogeneousCochains (TopRep.quotientInvariants U.toSubgroup X)
  map {U V} f := cochainsMap (quotientTransitionHom V U (leOfHom f))
    (quotientTransitionIncl X (leOfHom f))
  map_id U := quotientTransition_cochainsMap_id X U
  map_comp f g := quotientTransition_cochainsMap_comp X (leOfHom g) (leOfHom f)

end ContinuousCohomology
end
