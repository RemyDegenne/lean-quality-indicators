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

/-- The topology inherited by a restricted coefficient module from the full
invariant module at the same level. -/
abbrev topology (S : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) :
    TopologicalSpace (S.coefficients U) :=
  (L.topology U.toOpenSubgroup).induced
    ((↑) : S.coefficients U → openSubgroupInvariants A U.toOpenSubgroup)

end RestrictedLevelSystem
end ContinuousGroupCohomology.LevelCompact
end
end
