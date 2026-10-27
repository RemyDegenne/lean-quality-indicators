public section

namespace CFSG.RankThree.PartTwo.Sec11.Eii

open CFSG CFSG.Open CFSG.Goldschmidt

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_oddCoreOf_self (N : Subgroup G) :
    N ≤ Subgroup.normalizer (oddCoreOf N : Set G) :=
  Subgroup.le_normalizer.trans le_normalizer_oddCoreOf

end CFSG.RankThree.PartTwo.Sec11.Eii
end
