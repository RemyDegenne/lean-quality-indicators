public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenter

open Subgroup GomiFusion RootAxisTwoCore

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

open scoped Matrix

section General

variable {G : Type*} [Group G]

theorem relIndex_le_two {H K : Subgroup G} (h : ∃ a ∈ K, ∀ b ∈ K, b * a ∈ H ∨ b ∈ H) :
    H.relIndex K ≤ 2 :=
  Nat.le_of_dvd two_pos (relIndex_dvd_two_iff.mpr h)

end General
end FullCenter
end CFSG.LocalAnalysis.SymplecticFourStandard
end
