public section

set_option autoImplicit false

set_option warningAsError true

open CategoryTheory

noncomputable section

namespace ContinuousGroupCohomology

universe u

variable (R G : Type u) [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

namespace RestrictedLevelCompactRep

variable {R G}

/-- The canonical universal-norm restricted system. -/
@[expose] def universalNorm (A : LevelCompactRep.{u, u, u} R G) :
    RestrictedLevelCompactRep R G where
  toLevelCompactRep := A
  system := LevelCompact.universalNormRestrictedLevelSystem A.rep A.levelCompact

end RestrictedLevelCompactRep
end ContinuousGroupCohomology
end
end
