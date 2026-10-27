public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree TauCeti
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

set_option linter.unusedSectionVars false

section Reduction

theorem threeNonToralCubeRest_E8_of_normalizes (h : E8NonToralNormalizes) :
    ThreeNonToralCubeRest .E8 LieTypeIndex.E8 :=
  fun K _ _ hK hs E₀ hE₀ hc hN hD => (hN (h K hK hs E₀ hE₀ hc hD)).elim

end Reduction
end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
end
