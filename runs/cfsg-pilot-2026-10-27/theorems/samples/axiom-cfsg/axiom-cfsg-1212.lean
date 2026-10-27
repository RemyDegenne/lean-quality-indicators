public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)

variable {f : ℕ} {K : Type} [Field K]

theorem le_inSubgroup_perfectResidual' {H : Type*} [Group H] {P Y : Subgroup H} (hPY : P ≤ Y)
    (hP : Group.IsPerfect ↥P) : P ≤ inSubgroup perfectResidual Y :=
  CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf P Y hP hPY

end CFSG.RankThree.PartOne.LSTD
end
