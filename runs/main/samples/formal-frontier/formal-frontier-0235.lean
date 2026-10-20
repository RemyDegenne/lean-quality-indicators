public section

set_option autoImplicit false

set_option warningAsError true

open CategoryTheory

noncomputable section

namespace ContinuousGroupCohomology.LevelCompactRep

universe u

variable {R : Type u} [CommRing R]

variable {G : Type u} [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G] [CompactSpace G]

variable {A B : LevelCompactRep.{u, u, u} R G}

omit [IsTopologicalGroup G] [CompactSpace G] in
@[simp]
lemma groupMap_id (A : LevelCompactRep.{u, u, u} R G)
    (U : OpenSubgroup G) :
    groupMap (𝟙 A) U = 𝟙 (LevelCompact.group A.rep A.levelCompact U) := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  rfl

end ContinuousGroupCohomology.LevelCompactRep
end
end
