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

@[simp, reassoc]
lemma finiteCoinvariantsMap_comp {C : LevelCompactRep.{u, u, u} R G}
    (f : A ⟶ B) (g : B ⟶ C) (S : OpenNormalSubgroup G) :
    finiteCoinvariantsMap (f ≫ g) S =
      finiteCoinvariantsMap f S ≫ finiteCoinvariantsMap g S := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  induction x using Representation.Coinvariants.induction_on with
  | _ x => rfl

end ContinuousGroupCohomology.LevelCompactRep
end
end
