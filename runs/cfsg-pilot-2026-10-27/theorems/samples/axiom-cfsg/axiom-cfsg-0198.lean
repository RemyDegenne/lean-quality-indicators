public section

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.ComponentClassification.SporadicSchreierDispatch
  (SporadicSchreierCase sporadicSchreierCase_of_outer)

open CFSG.ComponentClassification.CatalogSchreierCases

namespace CFSG.RankThree.PartOne.SPOR

theorem sporadicSchreierCase_M :
    SporadicSchreierCase .M :=
  fun _ _ _ _ _ ⟨e⟩ => isSolvable_outer_of_simple_M e

end CFSG.RankThree.PartOne.SPOR
end
