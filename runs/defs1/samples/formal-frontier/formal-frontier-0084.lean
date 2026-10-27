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

/-- The coefficient module selected at an open normal level. -/
abbrev coefficients (S : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) :=
  (S.subrepresentation U).toSubmodule

end RestrictedLevelSystem
end ContinuousGroupCohomology.LevelCompact
end
end
