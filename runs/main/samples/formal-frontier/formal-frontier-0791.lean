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

@[reassoc]
lemma normFromFiniteCoinvariants_naturality_hom (f : A ⟶ B)
    (S : OpenNormalSubgroup G) :
    finiteCoinvariantsMap f S ≫
        LevelCompact.normFromFiniteCoinvariants B.rep B.levelCompact S =
      LevelCompact.normFromFiniteCoinvariants A.rep A.levelCompact S ≫
        groupMap f (⊤ : OpenSubgroup G) := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  exact normFromFiniteCoinvariants_naturality f S x

end ContinuousGroupCohomology.LevelCompactRep
end
end
