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

@[simp]
lemma finiteCoinvariantsMap_mk (f : A ⟶ B) (S : OpenNormalSubgroup G)
    (x : openSubgroupInvariants A.rep S.toOpenSubgroup) :
    finiteCoinvariantsMap f S
        (Representation.Coinvariants.mk
          (A.rep.quotientToInvariants S.toSubgroup).ρ x) =
      Representation.Coinvariants.mk
        (B.rep.quotientToInvariants S.toSubgroup).ρ
        (mapInvariants f S.toOpenSubgroup x) := by
  rfl

end ContinuousGroupCohomology.LevelCompactRep
end
end
