public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

open CFSG.Assembly.RankThreeEven (projSp)

open CFSG.Assembly.LowTwoRank (StatedScalars StatedProj StatedSp)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars glCongr_statedSp
  statedProjCongr)

open CFSG.RankThree.PartTwo.Sec4.Item434Kit

local instance decEqH8 : DecidableEq H8 := inferInstance

theorem outerRow_sp82 : OuterRow (projSp 4 (GaloisField 2 1)) := by
  haveI : Finite (projSp 4 (GaloisField 2 1)) := Finite.of_equiv _ sp82Equiv.symm.toEquiv
  exact outerRow_of_not_three_dvd_outer Item434SmallTwoIV.not_three_dvd_card_outer_projSp_four_two

end CFSG.RankThree.PartTwo.Sec4.RonanK432
end
