public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

open scoped commutatorElement Pointwise

theorem bThreePropertyCentral_of_bThreeProperty (h : BThreeProperty) : BThreePropertyCentral := by
  intro G _ _ H hH _ X hX b hbH hb3 hbX Y hYXC hYp hYsn hYq
  exact h G H hH X hX b hbH hb3 hbX Y hYXC hYp hYsn hYq

end CFSG.RankThree.PartTwo.Sec6
end
