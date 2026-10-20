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
lemma finiteTateNegOneMap_deflation (f : A ⟶ B)
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteTateNegOneMap f S ≫
        LevelCompact.finiteTateNegOneDeflation B.rep B.levelCompact S T hST =
      LevelCompact.finiteTateNegOneDeflation A.rep A.levelCompact S T hST ≫
        finiteTateNegOneMap f T := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  change
    LevelCompact.finiteCoinvariantDeflation B.rep B.levelCompact S T hST
        (finiteCoinvariantsMap f S x.1) =
      finiteCoinvariantsMap f T
        (LevelCompact.finiteCoinvariantDeflation A.rep A.levelCompact S T hST x.1)
  exact CategoryTheory.congr_fun (finiteCoinvariantsMap_deflation f S T hST) x.1

end ContinuousGroupCohomology.LevelCompactRep
end
end
