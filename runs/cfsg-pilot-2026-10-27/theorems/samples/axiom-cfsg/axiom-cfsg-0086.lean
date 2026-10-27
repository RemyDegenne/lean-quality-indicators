public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.Assembly.LowTwoRank (StatedSp)

open CFSG.Assembly.RankThreeEven (localRank projSp)

section Final

theorem fin812XNormal : Fin812XNormal := by
  intro G _ _ A c L a b X Y n h
  exact h.toSec8Pair.normalizer_zpowers_le_normalizer h.item89_X

end Final
end CFSG.RankThree.PartTwo.Sec8
end
