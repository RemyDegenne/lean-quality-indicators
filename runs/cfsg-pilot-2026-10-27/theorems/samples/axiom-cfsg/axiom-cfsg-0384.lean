public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

theorem e7Six_pow : (wordMat Tag.E7 e7SixWord) ^ 6 = 1 := by
  rw [e7Six_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

end CFSG.LieType.SeitzGeneration
end
