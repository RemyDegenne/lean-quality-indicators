public section

namespace CFSG.RankThree.PartTwo.KFacts.K412

open Equiv Subgroup CFSG.RankThree.PartTwo.KFacts.KP2

open scoped Pointwise

theorem commute_sylTenF : ∀ a b c l : Fin 3, l ≠ 0 → ∀ i j k : Fin 3,
    eTwentySevenF i j k * sylTenF a b c l = sylTenF a b c l * eTwentySevenF i j k →
      i = j ∧ j = k := by
  decide +kernel

end CFSG.RankThree.PartTwo.KFacts.K412
end
