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

/-- A level-compact coefficient morphism preserving each chosen restricted
coefficient module. -/
@[ext]
structure Hom (A B : RestrictedLevelCompactRep R G) where
  /-- The underlying level-compact morphism. -/
  hom : A.toLevelCompactRep ⟶ B.toLevelCompactRep
  /-- Preservation of the selected subrepresentation at each level. -/
  map_mem : ∀ (U : OpenNormalSubgroup G)
    (x : openSubgroupInvariants A.rep U.toOpenSubgroup),
    x ∈ A.system.subrepresentation U →
      LevelCompactRep.mapInvariants hom U.toOpenSubgroup x ∈
        B.system.subrepresentation U

end RestrictedLevelCompactRep
end ContinuousGroupCohomology
end
end
