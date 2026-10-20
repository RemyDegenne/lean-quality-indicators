public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

namespace RestrictedLevelSystem

variable {A : Rep.{u} R G} {L : LevelCompact A}

open CategoryTheory

/-- A restricted relative norm as a morphism of compact Hausdorff additive
groups. -/
def relativeNormHom (S : RestrictedLevelSystem A L)
    (U V : OpenNormalSubgroup G) (h : V ≤ U) :
    S.group V ⟶ S.group U := by
  apply ConcreteCategory.ofHom
  exact
    { toAddMonoidHom := (S.relativeNorm U V h).toAddMonoidHom
      continuous_toFun := S.continuous_relativeNorm U V h }

end RestrictedLevelSystem
end ContinuousGroupCohomology.LevelCompact
end
end
