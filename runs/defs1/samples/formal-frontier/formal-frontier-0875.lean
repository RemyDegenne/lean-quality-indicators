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

/-- A restricted coefficient module is compact in its inherited topology. -/
noncomputable abbrev compact (S : RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) :
    @CompactSpace (S.coefficients U) (S.topology U) := by
  let _ : TopologicalSpace (openSubgroupInvariants A U.toOpenSubgroup) :=
    L.topology U.toOpenSubgroup
  let _ : CompactSpace (openSubgroupInvariants A U.toOpenSubgroup) :=
    L.compact U.toOpenSubgroup
  exact isCompact_iff_compactSpace.mp (S.isClosed U).isCompact

end RestrictedLevelSystem
end ContinuousGroupCohomology.LevelCompact
end
end
