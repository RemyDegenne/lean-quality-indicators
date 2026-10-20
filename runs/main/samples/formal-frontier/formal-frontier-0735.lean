public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

variable (A : Rep.{u} R G) (L : LevelCompact A)

lemma finiteCoinvariantDeflation_comp
    (S T U : OpenNormalSubgroup G) (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteCoinvariantDeflation A L S T hST ≫
        finiteCoinvariantDeflation A L T U hTU =
      finiteCoinvariantDeflation A L S U (hST.trans hTU) := by
  apply ConcreteCategory.hom_ext
  intro x
  exact CategoryTheory.congr_fun
    (finiteNegativeDeflationCoinvariants_comp
      A S.toSubgroup T.toSubgroup U.toSubgroup hST hTU) x

end ContinuousGroupCohomology.LevelCompact
end
end
