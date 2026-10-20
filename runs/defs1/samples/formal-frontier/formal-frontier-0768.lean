public section

set_option autoImplicit false

set_option warningAsError true

open CategoryTheory

noncomputable section

namespace ContinuousGroupCohomology

universe u

variable (R G : Type u) [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- A level-compact representation with a chosen restricted coefficient system. -/
structure RestrictedLevelCompactRep where
  /-- The underlying level-compact representation. -/
  toLevelCompactRep : LevelCompactRep.{u, u, u} R G
  /-- The chosen closed residual subrepresentation at every open normal level. -/
  system : LevelCompact.RestrictedLevelSystem toLevelCompactRep.rep
    toLevelCompactRep.levelCompact

end ContinuousGroupCohomology
end
end
