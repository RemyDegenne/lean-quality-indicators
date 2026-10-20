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
@[simp, reassoc]
lemma groupMap_comp {C : LevelCompactRep.{u, u, u} R G}
    (f : A ⟶ B) (g : B ⟶ C) (U : OpenSubgroup G) :
    groupMap (f ≫ g) U = groupMap f U ≫ groupMap g U := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  rfl

end ContinuousGroupCohomology.LevelCompactRep
end
end
