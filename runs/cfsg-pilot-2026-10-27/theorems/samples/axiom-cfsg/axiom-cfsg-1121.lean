public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.ABGLocalTools

open CFSG.GorensteinWalter (IsComponentOf generalizedFittingSubgroupOf componentLayerOf)

open scoped commutatorElement

open CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem pRank_top_le_three (h69 : R6_9 Dat) (K : Subgroup m.Hbar) :
    CFSG.Open.pRank m.r (⊤ : Subgroup ↥K) ≤ 3 := by
  have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective m.r m.hr
    K.subtype K.subtype_injective (⊤ : Subgroup ↥K)
  exact h1.trans (m.pRank_Hbar_le_three h69 _)

end Mz614
end CFSG.LocalAnalysis.UniquenessCase.UC6G
end
