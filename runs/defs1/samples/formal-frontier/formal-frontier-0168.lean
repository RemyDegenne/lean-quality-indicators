public section

set_option warningAsError true

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace ContinuousGroupCohomology

universe uR uG uA

variable (R : Type uR) [CommRing R]

variable (G : Type uG) [Group G] [TopologicalSpace G]

namespace LevelCompactRep

variable {R G}

/-- A morphism of level-compact representations is a representation morphism
whose restriction to invariants at every open subgroup is continuous for the
specified level topologies. -/
@[ext]
structure Hom (A B : LevelCompactRep.{uR, uG, uA} R G) where
  /-- The underlying representation morphism. -/
  hom : A.rep ⟶ B.rep
  /-- Continuity at every open-subgroup invariant level. -/
  continuous_invariants : ∀ U : OpenSubgroup G,
    @Continuous (openSubgroupInvariants A.rep U)
      (openSubgroupInvariants B.rep U)
      (A.levelCompact.topology U) (B.levelCompact.topology U)
      (invariantsMap hom U)

end LevelCompactRep
end ContinuousGroupCohomology
end
end
