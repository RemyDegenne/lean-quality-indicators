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

/-- The map on invariants induced by a level-compact morphism. -/
abbrev mapInvariants {A B : LevelCompactRep.{uR, uG, uA} R G} (f : A ⟶ B)
    (U : OpenSubgroup G) :
    openSubgroupInvariants A.rep U →ₗ[R] openSubgroupInvariants B.rep U :=
  invariantsMap f.hom U

end LevelCompactRep
end ContinuousGroupCohomology
end
end
