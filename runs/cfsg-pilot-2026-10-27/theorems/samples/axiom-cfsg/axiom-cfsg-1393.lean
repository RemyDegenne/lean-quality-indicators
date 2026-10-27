public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

open scoped commutatorElement

section Block

variable {G : Type*} [Group G]

theorem blockU_le (L : Subgroup G) : blockU L ≤ L :=
  (blockU_le_pCoreOf L).trans (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L)

end Block
end CFSG.QuasithinUnique.Lin2
end
